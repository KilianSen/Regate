from __future__ import annotations

import json
import sys
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

import lean_check
import lean_prover
import lean_induction

PROTOCOL = "1.0"
BACKEND = "leanregate"
VERSION = "0.1.0"


class RequestError(ValueError):
    pass


_LEAF_TYPES = {"number", "variable", "wild"}


def _validate_node(node, where: str, depth: int = 0) -> None:
    """Structurally validate a MathNode so a malformed one is a 400, not a crash.

    check_induction dereferences goal slots by name (`goal["slots"]["left"][0]`); a
    goal without them would raise an uncaught KeyError. This enforces the shape up
    front — leaves carry a `value`, everything else a `slots` dict of child lists —
    and caps depth so a pathological tree cannot overflow the stack.
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


def _envelope(outcome, score, certified, **extra):
    base = {"protocol": PROTOCOL, "backend": BACKEND, "backend_version": VERSION,
            "outcome": outcome, "score": score, "certified": certified,
            "proof": None, "witness": None, "steps": None, "hint": None,
            "feedback": "", "meta": {}}
    base.update(extra)
    return base


def _prove_ruleset(ex: dict) -> tuple[dict, dict]:
    """Rules come from the API. Prove the transmitted `exercise.ruleset` at request
    time with a Lean kernel (lean_prover); return (proven-rule table, meta). Rules
    Lean cannot prove — or all of them, when the toolchain is absent — are simply
    absent from the table, so any step using them grades `unknown`, never falsely.
    Leanregate has no built-in catalogue; an empty ruleset means nothing certifies."""
    ruleset = ex.get("ruleset")
    if not ruleset:
        return {}, {}
    results = lean_prover.prove_ruleset(ruleset)
    meta = {"ruleset": {rid: {"proven": r.proven, "method": r.method,
                              "lemma": r.lemma, "detail": r.detail}
                        for rid, r in results.items()}}
    table: dict = {}
    if lean_prover.lean_available():
        for rule in ruleset:
            res = results.get(str(rule.get("id")))
            if res and res.proven:
                pr = lean_check.proven_from_custom(rule, res.lemma)
                table[pr.id] = pr
    return table, meta


def grade(request: dict) -> dict:
    if request.get("protocol", PROTOCOL).split(".")[0] != PROTOCOL.split(".")[0]:
        raise RequestError(f"unsupported protocol {request.get('protocol')!r}")
    ex = request.get("exercise") or {}
    sub = request.get("submission") or {}

    # Rules come from the API: prove the transmitted ruleset at request time. This
    # table feeds both the induction obligations and ordinary derivations.
    rules_table, meta = _prove_ruleset(ex)

    # Induction is exactly where a formal backend earns its keep. We grade the
    # STUDENT's submission: certify their base-case and inductive-step derivations
    # (the inductive step may substitute the hypothesis P(k)) against the proven
    # rules + transmitted definitions. Only if both obligations check do we run
    # lean_induction as a kernel backstop — it proves ∀n.P(n) via Nat.rec and guards
    # against inconsistent definitions. An empty or wrong proof is never certified.
    if ex.get("mode") == "induction":
        if not ex.get("goal"):
            raise RequestError("induction mode requires exercise.goal")
        _validate_node(ex["goal"], "exercise.goal")
        rep = lean_check.check_induction(ex, sub, rules_table)
        meta["induction"] = {"var": ex.get("inductionVar"), "submission": rep.status,
                             "reason": rep.reason}
        if rep.status == "invalid":
            return _envelope("invalid_derivation", 0, False, meta=meta,
                             feedback=f"Invalid induction proof: {rep.reason}.")
        if rep.status == "uncertifiable":
            return _envelope("unknown", None, False, meta=meta,
                             feedback=f"Leanregate could not certify this induction: "
                                      f"{rep.reason}. Route to review.")
        # Both obligations certified — backstop with the Lean kernel.
        res = lean_induction.certify(ex)
        meta["induction"]["leanBackstop"] = res.method
        meta["induction"]["detail"] = res.detail
        if res.certified:
            # `certified: true` owes the caller something re-checkable. The proof is
            # the Lean file the kernel accepted, plus the lemma names each step was
            # certified against: run `lean` on it and you get the same verdict.
            try:
                source = lean_induction.build_source(ex)
            except lean_induction.InductionError:   # cannot happen: certify() built it
                source = ""
            proof = [{"engine": "lean", "method": "induction",
                      "theorem": lean_induction.THEOREM, "source": source}]
            return _envelope("proven_equal", 100, True, meta=meta, proof=proof,
                             feedback="Certified: base case and inductive step verified; "
                                      "∀n. P(n) follows by Lean induction (Nat.rec). "
                                      "The accepted Lean source is attached as the proof.")
        reason = {"unavailable": "the Lean toolchain is unavailable in this deployment",
                  "untranslatable": f"the goal is outside the certifiable fragment ({res.detail})",
                  "rejected": "Lean could not confirm the inductive claim"}.get(res.method, res.detail)
        return _envelope("unknown", None, False, meta=meta,
                         feedback=f"Base and step verified, but the Lean backstop did not "
                                  f"certify the goal: {reason}. Route to review.")
    if "source" not in ex:
        raise RequestError("exercise.source is required")
    if ex.get("mode", "transformation") == "transformation" and ex.get("target") is None:
        raise RequestError("transformation mode requires exercise.target")
    if sub.get("final") is None and not sub.get("steps"):
        raise RequestError("submission must have a final expression or steps")

    mode = ex.get("mode", "transformation")
    target = ex.get("target")
    source = ex["source"]

    # 1) A submitted derivation: certify it step-by-step against the rules proven
    #    for this request (the transmitted ruleset). With no proven rules — an empty
    #    ruleset, or no Lean toolchain — every rule step is uncertifiable → unknown.
    if sub.get("steps"):
        report = lean_check.check_derivation(source, sub["steps"], rules_table)
        if report.status == "invalid":
            return _envelope("invalid_derivation", 0, False, steps=report.steps_out, meta=meta,
                             feedback=f"step {report.invalid_index} invalid: {report.reason}")
        if report.status == "uncertifiable":
            return _envelope("unknown", None, False, steps=report.steps_out, meta=meta,
                             feedback=f"step {report.invalid_index} not certifiable "
                                      f"({report.reason}); route to review.")
        final = report.final
        proof = _proof_from(sub["steps"], report.steps_out)
        if _reached_goal(mode, final, target):
            return _envelope("proven_equal", 100, True, steps=report.steps_out, proof=proof,
                             meta=meta,
                             feedback="Valid derivation; every step is an instance of a "
                                      "rule the Lean kernel proved for this request.")
        # Certified steps but not at the goal form: Leanregate does not grade
        # value-equivalence or partial credit (that is Eggregate's job).
        return _envelope("unknown", None, False, steps=report.steps_out, proof=proof, meta=meta,
                         feedback="Each step is Lean-certified but the derivation does not "
                                  "reach the target form; route to review.")

    # 2) No derivation, just a final expression. Decidable without any rule: a
    #    final that *is* the target form (or, in equation mode, a reflexive
    #    a = a) is correct regardless of path — structural equality on MathNode.
    final = sub.get("final")
    if final is not None and _reached_goal(mode, final, target):
        # The empty proof is the certificate: zero rewrites are needed, the terms are
        # structurally identical. `proof: []` says "checked, nothing to do"; `null`
        # would say "certified, but nothing to show for it" — a protocol violation.
        return _envelope("proven_equal", 100, True, meta=meta, proof=[],
                         feedback="Reached the target form." if mode != "equation"
                                  else "Both sides are identical — the equation holds.")

    # Everything else — value-equivalence and partial credit — needs equality
    # reasoning Leanregate does not do; be honestly inconclusive.
    return _envelope("unknown", None, False, meta=meta,
                     feedback="Leanregate grades formal derivations and exact target forms; "
                              "value-equivalence without a derivation is out of scope — "
                              "route to review or use the Eggregate backend.")


def _reached_goal(mode: str, final: dict, target) -> bool:
    """Did the endpoint reach the goal? Transformation: equals target. Equation:
    a reflexive `a = a` (both sides structurally identical)."""
    if mode == "equation":
        return (isinstance(final, dict) and final.get("type") == "eq"
                and final.get("slots", {}).get("left") == final.get("slots", {}).get("right"))
    return target is not None and final == target


def _proof_from(steps_in: list, steps_out: list) -> list:
    """Pair each input step with the Lean lemma that certified it."""
    proof = []
    for si, so in zip(steps_in, steps_out):
        proof.append({"rule": si.get("rule"), "path": si.get("path", []),
                      "direction": si.get("direction", "forward"),
                      "lemma": so["reason"].removeprefix("Lean: "),
                      "state": si.get("result")})
    return proof


# ---- transports (mirror Eggregate's server.py) ----------------------------
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
                             "version": VERSION, "protocol": PROTOCOL})
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
