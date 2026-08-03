from __future__ import annotations

import json
import sys
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

import cvc5_equiv
import cvc5_induction
import cvc5_prover
import step_check

PROTOCOL = "1.1"
BACKEND = "cvc5regate"
VERSION = "0.1.0"


class RequestError(ValueError):
    pass


_LEAF_TYPES = {"number", "variable", "wild"}


def _validate_node(node, where: str, depth: int = 0) -> None:
    """Structurally validate a MathNode so a malformed one is a 400, not a crash.

    The induction translator dereferences slots by name (`s["left"][0]`); a goal
    without them raised an uncaught KeyError (HTTP 500 / CLI exit 1). This enforces
    the shape up front — leaves carry a `value`, everything else a `slots` dict of
    child lists — and caps depth so a pathological tree cannot overflow the stack.
    """
    if depth > 200:
        raise RequestError(f"{where}: expression nested too deeply")
    if not isinstance(node, dict):
        raise RequestError(f"{where}: expected a MathNode object")
    t = node.get("type")
    if not isinstance(t, str):
        raise RequestError(f"{where}: MathNode is missing a string 'type'")
    if t in _LEAF_TYPES:
        if "value" not in node:
            raise RequestError(f"{where}: {t} node needs a 'value'")
        return
    slots = node.get("slots")
    if not isinstance(slots, dict):
        raise RequestError(f"{where}: {t!r} node needs a 'slots' object")
    for name, kids in slots.items():
        if not isinstance(kids, list):
            raise RequestError(f"{where}: slot {name!r} must be a list")
        for k in kids:
            _validate_node(k, where, depth + 1)


def _validate_assumptions(ex: dict) -> None:
    """`exercise.assumptions` is grading input on every path (it scopes the domain the
    counterexample search may range over), so a malformed one is a 400 — not a crash,
    and certainly not a silently ignored field. The *kind* is not judged here: an
    untranslatable kind is a well-formed request this backend declines (`unknown`)."""
    raw = ex.get("assumptions")
    if raw is None:
        return
    if not isinstance(raw, list):
        raise RequestError("exercise.assumptions must be a list")
    for i, a in enumerate(raw):
        if not isinstance(a, dict) or not isinstance(a.get("kind"), str) or "value" not in a:
            raise RequestError(
                f"exercise.assumptions[{i}]: each assumption needs a string 'kind' "
                f"and a MathNode 'value'")
        _validate_node(a["value"], f"exercise.assumptions[{i}].value")


def _envelope(outcome, score, certified, **extra):
    base = {"protocol": PROTOCOL, "backend": BACKEND, "backend_version": VERSION,
            "outcome": outcome, "score": score, "certified": certified,
            "proof": None, "witness": None, "steps": None, "hint": None,
            "feedback": "", "meta": {}}
    base.update(extra)
    return base


def grade(request: dict) -> dict:
    if request.get("protocol", PROTOCOL).split(".")[0] != PROTOCOL.split(".")[0]:
        raise RequestError(f"unsupported protocol {request.get('protocol')!r}")
    ex = request.get("exercise") or {}

    _validate_assumptions(ex)

    mode = ex.get("mode", "transformation")
    if mode == "induction":
        return _grade_induction(ex, request.get("submission") or {})
    if mode not in ("transformation", "equation"):
        raise RequestError(f"unsupported mode {mode!r}")

    if "goal" not in ex and "source" not in ex:
        raise RequestError("exercise must have a 'goal' (induction) or 'source'")
    return _grade_equational(ex, request.get("submission") or {})


def _grade_induction(ex: dict, sub: dict) -> dict:
    # GRADE THE STUDENT'S derivation, not just the bare theorem: each submitted
    # step becomes an SMT validity query (the inductive step under the IH). A
    # value-changing step is `sat` → invalid_derivation; both obligations reducing
    # to `t = t` certify the induction. A missing/half-empty submission, or a step
    # cvc5 cannot decide, is `unknown` (route to review) — never an auto-pass on a
    # true theorem the student did not prove. (The bare theorem certifier +
    # disprove witness, `cvc5_induction.certify`, remains for the authoring-time
    # "is this exercise certifiable?" oracle, but never stands in as a grade.)
    if not ex.get("goal"):
        raise RequestError("induction mode requires exercise.goal")
    if not ex.get("inductionVar"):
        raise RequestError("induction mode requires exercise.inductionVar")
    _validate_node(ex["goal"], "exercise.goal")

    res = cvc5_induction.grade_derivation(ex, sub)
    meta = {"induction": {"var": ex.get("inductionVar"), "engine": "cvc5",
                          "status": res.status, "reason": res.reason}}
    if res.ruleset is not None:
        meta["ruleset"] = res.ruleset
    if res.status == "certified":
        # `certified: true` owes the caller something re-checkable. cvc5 1.3.x cannot
        # export an Alethe proof for an induction (skolems), so the certificate is the
        # exact SMT-LIB the solver accepted: any SMT solver can re-run it and get the
        # same `unsat`. Weaker than an independent kernel check — meta.rechecked says
        # so — but reproducible rather than a bare assertion.
        return _envelope("proven_equal", 100, True, meta={**meta, "rechecked": False},
                         proof=[{"engine": "cvc5", "method": "quant-ind",
                                 "smtlib": res.smtlib, "expect": "unsat"}],
                         feedback="Certified: every step of your base case and inductive step "
                                  "applies a cvc5-proven rule; ∀n. P(n) follows by induction. "
                                  "The SMT-LIB problem is attached; re-run it to re-check.")
    if res.status == "refuted":
        return _envelope("proven_unequal", 0, True, meta=meta, witness=res.witness,
                         feedback=f"The goal does not hold: cvc5 found a counterexample "
                                  f"({', '.join(f'{k}={v}' for k, v in res.witness.items())}).")
    if res.status == "invalid":
        return _envelope("invalid_derivation", 0, False, meta=meta,
                         feedback=f"Invalid induction proof: {res.reason}.")
    reason = {"unattempted": "no derivation submitted to grade",
              "unavailable": "the cvc5 toolchain is unavailable in this deployment",
              "untranslatable": f"the goal is outside the gradeable fragment ({res.reason})"}.get(
                  res.status, res.reason)
    return _envelope("unknown", None, False, meta=meta,
                     feedback=f"cvc5regate could not grade this induction: {reason}. "
                              "Route to review.")


# ---------------------------------------------------------------------------
# Non-induction grading (mode "transformation" / "equation").
#
# Two engines, strongest first: (1) if a `steps` derivation is submitted, certify
# it symbolically against the transmitted ruleset (each step an instance of a
# trusted/proven rule — same strict check as the induction obligations, no solver
# needed); (2) the cvc5 SMT equivalence oracle disproves-first (a numeric
# counterexample → proven_unequal) then proves `source ≡ target`. The oracle also
# backstops a valid-but-unfinished or uncertifiable derivation by grading the
# endpoint the student reached. Outcome/score semantics mirror eggregate.
# ---------------------------------------------------------------------------
def _grade_equational(ex: dict, sub: dict) -> dict:
    mode = ex.get("mode", "transformation")
    if "source" not in ex:
        raise RequestError("exercise.source is required")
    if mode == "transformation" and ex.get("target") is None:
        raise RequestError("transformation mode requires exercise.target")
    if sub.get("final") is None and not sub.get("steps"):
        raise RequestError("submission must have a final expression or steps")

    _validate_node(ex["source"], "exercise.source")
    target = ex.get("target")
    if target is not None:
        _validate_node(target, "exercise.target")
    source = ex["source"]
    ac = step_check.ac_ops(ex)
    partial = bool((ex.get("options") or {}).get("partial_credit", True))
    meta: dict = {}
    steps_out = None
    final = None

    # 1) A submitted derivation: certify it step-by-step. Rules are trusted by default
    #    (Regate's ruleset warrant); `options.verify_rules` re-proves each with cvc5.
    #    A transformation derivation needs no solver — a valid chain of trusted rule
    #    instances reaching the target IS the proof.
    if sub.get("steps"):
        proven = cvc5_induction.prove_ruleset(ex)
        meta["ruleset"] = {rid: {"proven": p.proven, "method": p.method}
                           for rid, p in proven.items()}
        rules = step_check.build_rules(ex, {rid for rid, p in proven.items() if p.proven})
        report = step_check.check_derivation(source, sub["steps"], rules, ac)
        steps_out = report.steps_out
        if report.status == "invalid":
            return _envelope("invalid_derivation", 0, False, steps=steps_out, meta=meta,
                             feedback=f"step {report.invalid_index} invalid: {report.reason}")
        if report.status == "valid":
            final = report.final
            if _reached(mode, final, target, ac):
                return _envelope("proven_equal", 100, True, steps=steps_out, meta=meta,
                                 proof=_derivation_proof(sub["steps"]),
                                 feedback="Valid derivation; every step is an instance of a "
                                          "trusted/proven rule and it reaches the target form.")
            # valid but unfinished → grade the endpoint the student reached.
        else:
            # Uncertifiable: this backend cannot LICENSE these steps — a Type-B/Leibniz
            # substitution, a guarded rule with no discharging assumption, or an unproven
            # lemma. It may still DISPROVE the claimed endpoint: a counterexample is a fact
            # about expressions and is sound whatever the step licences were. What it must
            # not do is award credit.
            #
            # This used to set `final = sub["steps"][-1].get("result")` and fall through to
            # endpoint grading unconditionally, so an unlicensed step whose claimed result
            # equalled the target scored proven_equal / 100 / certified — fixtures 14
            # (assumption-missing), 16 (leibniz-no-hypothesis) and 18 (broken-lemma) all did,
            # where eggregate returns invalid_derivation. Trivially exploitable: assert the
            # target as your step result and cite anything. GRADING_PROTOCOL §4.5.2 says a
            # backend that cannot model the request declines; it does not answer an easier one.
            claimed = sub["steps"][-1].get("result")
            if claimed is not None and mode == "transformation" and target is not None:
                _validate_node(claimed, "submission.steps[-1].result")
                v = cvc5_equiv.decide_equivalence(ex, claimed, target)
                if v.outcome == "proven_unequal" and v.witness:
                    return _envelope("proven_unequal", 0, True, witness=v.witness,
                                     steps=steps_out,
                                     meta={**meta, "equiv": {"method": v.method,
                                                             "rechecked": v.rechecked}},
                                     feedback="The derivation could not be certified, and the "
                                              "expression you reached is not equivalent to the "
                                              "goal (cvc5 found a counterexample).")
            return _envelope("unknown", None, False, steps=steps_out, meta=meta,
                             feedback=("the derivation uses a step this backend cannot license "
                                       f"({report.reason}); route to review."))

    # 2) Endpoint equivalence via the cvc5 oracle.
    if final is None:
        final = sub.get("final")
    if final is None:
        return _envelope("unknown", None, False, steps=steps_out, meta=meta,
                         feedback="the derivation could not be certified and no final "
                                  "expression was supplied; route to review.")
    _validate_node(final, "submission.final")

    if mode == "equation":
        return _grade_equation_endpoint(ex, final, ac, steps_out, meta)
    return _grade_transformation_endpoint(ex, source, final, target, ac, partial, steps_out, meta)


def _reached(mode: str, final, target, ac: tuple) -> bool:
    """Did the endpoint reach the goal? Transformation: equals target (up to AC).
    Equation: a reflexive `a = a`."""
    if not isinstance(final, dict):
        return False
    if mode == "equation":
        s = final.get("slots") or {}
        return (final.get("type") == "eq" and bool(s.get("left") and s.get("right"))
                and step_check.ac_equal(s["left"][0], s["right"][0], ac))
    return target is not None and step_check.ac_equal(final, target, ac)


def _derivation_proof(steps: list) -> list:
    """A certified transformation derivation's certificate: the ordered rule instances."""
    return [{"rule": s.get("rule"), "path": s.get("path", []),
             "direction": s.get("direction", "forward"), "state": s.get("result")}
            for s in steps if s.get("kind") != "B"]


def _equiv_proof(v: cvc5_equiv.EquivResult) -> list:
    """The oracle's re-runnable certificate for a proven equivalence."""
    proof = [{"engine": "cvc5", "method": v.method, "smtlib": v.smtlib, "expect": "unsat"}]
    if v.alethe:
        proof[0]["alethe"] = v.alethe
    return proof


def _grade_transformation_endpoint(ex, source, final, target, ac, partial, steps_out, meta) -> dict:
    if step_check.ac_equal(final, target, ac):
        # Endpoint grading, no solver: the exercise author warrants that `source` and `target`
        # are equivalent, so a `final` matching the target is credited on that warrant. Weak by
        # construction — the target is visible to the student — which is why the STEP path above
        # is the one that must not be bypassed, and why an unlicensed derivation now declines
        # rather than falling through to here. A malformed exercise (source NOT equivalent to
        # target) will still be credited here; that is the author's error, not the student's.
        return _envelope("proven_equal", 100, True, proof=[], steps=steps_out, meta=meta,
                         feedback="Reached the target form.")
    v = cvc5_equiv.decide_equivalence(ex, final, target)
    meta = {**meta, "equiv": {"method": v.method, "rechecked": v.rechecked}}
    if v.outcome == "proven_unequal":
        return _envelope("proven_unequal", 0, True, witness=v.witness, steps=steps_out, meta=meta,
                         feedback="Not equivalent to the goal (cvc5 found a counterexample).")
    if v.outcome == "proven_equal":
        d0 = max(1, cvc5_equiv.distance(source, target))
        df = cvc5_equiv.distance(final, target)
        score = 0 if (not partial or df >= d0) else max(1, min(99, int((1 - df / d0) * 100)))
        return _envelope("proven_equal", score, True, proof=_equiv_proof(v), steps=steps_out,
                         meta=meta,
                         feedback="Equivalent to the goal but not yet in the required form; "
                                  "keep simplifying.")
    if v.outcome == "equal_no_certificate":
        return _envelope("equal_no_certificate", None, False, steps=steps_out, meta=meta,
                         feedback="Believed equivalent but no independently re-checked "
                                  "certificate is available; route to review.")
    return _envelope("unknown", None, False, steps=steps_out, meta=meta,
                     feedback=f"cvc5 could not prove or disprove equivalence to the goal "
                              f"({v.detail[:200]}); route to review.")


def _grade_equation_endpoint(ex, final, ac, steps_out, meta) -> dict:
    s = final.get("slots") or {}
    if final.get("type") != "eq" or not (s.get("left") and s.get("right")):
        return _envelope("invalid_derivation", 0, False, steps=steps_out, meta=meta,
                         feedback="equation mode expects an equality (eq) expression.")
    lhs, rhs = s["left"][0], s["right"][0]
    if step_check.ac_equal(lhs, rhs, ac):
        return _envelope("proven_equal", 100, True, proof=[], steps=steps_out, meta=meta,
                         feedback="Both sides are identical — the equation holds.")
    v = cvc5_equiv.decide_equivalence(ex, lhs, rhs)
    meta = {**meta, "equiv": {"method": v.method, "rechecked": v.rechecked}}
    if v.outcome == "proven_unequal":
        return _envelope("proven_unequal", 0, True, witness=v.witness, steps=steps_out, meta=meta,
                         feedback="The two sides are not equal (cvc5 found a counterexample).")
    if v.outcome == "proven_equal":
        return _envelope("proven_equal", 100, True, proof=_equiv_proof(v), steps=steps_out,
                         meta=meta,
                         feedback="The two sides are equivalent — the equation holds.")
    if v.outcome == "equal_no_certificate":
        return _envelope("equal_no_certificate", None, False, steps=steps_out, meta=meta,
                         feedback="Believed to hold but no independently re-checked "
                                  "certificate is available; route to review.")
    return _envelope("unknown", None, False, steps=steps_out, meta=meta,
                     feedback=f"cvc5 could not prove or disprove the equation "
                              f"({v.detail[:200]}); route to review.")


# ---- transports (mirror leanregate's grade.py / eggregate's server.py) -----
def run_cli() -> int:
    try:
        request = json.load(sys.stdin)
    except json.JSONDecodeError as e:
        json.dump({"error": f"invalid JSON: {e}"}, sys.stdout)
        return 2
    try:
        json.dump(grade(request), sys.stdout)
        sys.stdout.write("\n")
        return 0
    except RequestError as e:
        json.dump({"error": str(e)}, sys.stdout)
        return 2


class _Handler(BaseHTTPRequestHandler):
    def _send(self, code, body):
        data = json.dumps(body).encode()
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(data)))
        self.end_headers()
        self.wfile.write(data)

    def do_GET(self):
        if self.path.rstrip("/") == "/health":
            self._send(200, {"status": "ok", "backend": BACKEND,
                             "version": VERSION, "protocol": PROTOCOL,
                             "cvc5": cvc5_prover.cvc5_available(),
                             "carcara": cvc5_prover.carcara_available()})
        else:
            self._send(404, {"error": "not found"})

    def do_POST(self):
        if self.path.rstrip("/") != "/grade":
            return self._send(404, {"error": "not found"})
        length = int(self.headers.get("Content-Length", 0))
        try:
            request = json.loads(self.rfile.read(length) or b"{}")
        except json.JSONDecodeError as e:
            return self._send(400, {"error": f"invalid JSON: {e}"})
        try:
            self._send(200, grade(request))
        except RequestError as e:
            self._send(400, {"error": str(e)})
        except Exception as e:
            self._send(500, {"error": f"internal error: {type(e).__name__}"})

    def log_message(self, *a):
        pass


def run_http(host="0.0.0.0", port=8000) -> int:
    server = ThreadingHTTPServer((host, port), _Handler)
    sys.stderr.write(f"{BACKEND} {VERSION} (protocol {PROTOCOL}) on http://{host}:{port}\n")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    return 0


if __name__ == "__main__":
    raise SystemExit(run_cli() if "--cli" in sys.argv else run_http())
