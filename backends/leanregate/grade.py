"""Leanregate grading entrypoint — conforms to the shared grading protocol.

    python grade.py            # HTTP: POST /grade, GET /health  (port 8000)
    python grade.py --cli      # CLI:  GradeRequest stdin -> GradeResponse stdout

Self-contained (stdlib only); shares no code with Eggregate — it shares only the
*protocol* (GRADING_PROTOCOL.md), which is the point.

Grading is *formal*: a submitted derivation is graded step-by-step by
`lean_check`, which certifies each step is an instance of a lemma **proven in
`Leanregate/Basic.lean`**. A derivation whose every step is certified and whose
endpoint reaches the target (or, in equation mode, a reflexive `a = a`) is
`proven_equal` with `certified=true`, its proof carrying the Lean lemma names.
Anything Lean has not proven — a guarded fraction rule's side condition, an
unknown rule, value-equivalence without a derivation — returns `unknown`:
honestly inconclusive, never a false grade.
"""
from __future__ import annotations

import json
import sys
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

import lean_check
import lean_prover

PROTOCOL = "1.0"
BACKEND = "leanregate"
VERSION = "0.1.0"


class RequestError(ValueError):
    pass


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
    sub = request.get("submission") or {}

    # Induction is exactly where a formal backend should shine — but certifying the
    # base∧step ⟹ ∀n leap needs a real Lean kernel run (`induction`/`Nat.rec`),
    # which is not yet wired. Until then, honestly inconclusive (never a false grade).
    if ex.get("mode") == "induction":
        return _envelope("unknown", None, False,
                         feedback="Leanregate: certifying an induction proof requires a Lean "
                                  "kernel run (Nat.rec) that is not yet wired. Route to review.")
    if "source" not in ex:
        raise RequestError("exercise.source is required")
    if ex.get("mode", "transformation") == "transformation" and ex.get("target") is None:
        raise RequestError("transformation mode requires exercise.target")
    if sub.get("final") is None and not sub.get("steps"):
        raise RequestError("submission must have a final expression or steps")

    mode = ex.get("mode", "transformation")
    target = ex.get("target")
    source = ex["source"]

    # A formal backend may only grade with rules it has a proof for. The built-in
    # `rules` ids map to lemmas in Basic.lean / lean_check.PROVEN. An inline
    # `ruleset` arrives from a trusted author on the wire: rather than reject it,
    # we *prove each rule at request time* with a Lean kernel in the container
    # (lean_prover, hybrid ring/field_simp + proof-carrying). A rule Lean cannot
    # prove is dropped from the table, so any step using it grades `unknown` —
    # the same honesty as the scaffold, now extended to dynamic rulesets.
    rules_table = None       # None => the built-in BY_ID catalogue
    meta: dict = {}
    if ex.get("ruleset"):
        results = lean_prover.prove_ruleset(ex["ruleset"])
        meta = {"ruleset": {rid: {"proven": r.proven, "method": r.method,
                                  "lemma": r.lemma, "detail": r.detail}
                            for rid, r in results.items()}}
        if not lean_prover.lean_available():
            return _envelope("unknown", None, False, meta=meta,
                             feedback="Leanregate cannot prove the inline ruleset: the Lean "
                                      "toolchain is unavailable in this deployment. Use "
                                      "built-in rule ids or the Eggregate backend.")
        rules_table = {}
        for rule in ex["ruleset"]:
            res = results.get(str(rule.get("id")))
            if res and res.proven:
                pr = lean_check.proven_from_custom(rule, res.lemma)
                rules_table[pr.id] = pr

    # 1) A submitted derivation: certify it step-by-step against the proven table
    #    (built-in catalogue, or the runtime-proven custom ruleset).
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
                                      "Lean-proven lemma.")
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
        return _envelope("proven_equal", 100, True, meta=meta,
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
