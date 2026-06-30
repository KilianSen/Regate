"""cvc5regate grading entrypoint — conforms to the shared grading protocol.

    python grade.py            # HTTP: POST /grade, GET /health  (port 8000)
    python grade.py --cli      # CLI:  GradeRequest stdin -> GradeResponse stdout

Self-contained (stdlib only — the cvc5 binary is an external process); shares no
code with eggregate or leanregate — only the *protocol* (GRADING_PROTOCOL.md).

cvc5regate is an **induction certifier**: the third sibling backend. It fills the
same role leanregate fills with Lean — certifying the `base ∧ step ⟹ ∀n.P(n)`
schema that an equational backend (eggregate) can only *assume* — but with the
cvc5 SMT solver instead of Lean + Mathlib. That makes it far lighter (a ~20 MB
solver binary vs ~9 GB of Lean+Mathlib) and broader: cvc5 has native structural
induction and certifies goals **outside leanregate's equality-only emitter** —
inequalities (`2ⁿ ≥ 1`), divisibility (`3 ∣ n³−n`), and goals over recursive
functions beyond a single `pow` (e.g. a sum). It also *disproves* a false claim
with a concrete numeric witness.

Honest by construction: cvc5 `unsat` ⇒ certified `proven_equal`; `sat` with a
model ⇒ `proven_unequal` carrying the witness; `unknown` / timeout / a goal
outside the supported fragment / an absent toolchain ⇒ `unknown` — never a false
grade. (Non-induction equational grading is eggregate's / leanregate's job; for
those modes cvc5regate is honestly inconclusive.)
"""
from __future__ import annotations

import json
import sys
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

import cvc5_induction
import cvc5_prover

PROTOCOL = "1.0"
BACKEND = "cvc5regate"
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

    if ex.get("mode") == "induction":
        return _grade_induction(ex)

    # cvc5regate is an induction certifier. Equational derivations / endpoint
    # equivalence are graded by eggregate (e-graph) or leanregate (formal); this
    # backend is honestly inconclusive on them rather than guessing.
    if "goal" not in ex and "source" not in ex:
        raise RequestError("exercise must have a 'goal' (induction) or 'source'")
    return _envelope("unknown", None, False,
                     feedback="cvc5regate certifies inductive goals (mode='induction'); "
                              "equational derivations are out of scope — use the "
                              "eggregate or leanregate backend, or route to review.")


def _grade_induction(ex: dict) -> dict:
    if not ex.get("goal"):
        raise RequestError("induction mode requires exercise.goal")
    if not ex.get("inductionVar"):
        raise RequestError("induction mode requires exercise.inductionVar")

    res = cvc5_induction.certify(ex)
    meta = {"induction": {"var": ex.get("inductionVar"), "method": res.method,
                          "engine": "cvc5", "detail": res.detail}}

    if res.outcome == "proven_equal":
        # The certificate: cvc5's verdict (re-checked by Carcara when an Alethe
        # proof is exportable). The proof field carries the machine-checkable goal
        # + engine so the verdict is reproducible.
        meta["induction"]["rechecked"] = (res.method == "alethe+carcara")
        return _envelope("proven_equal", 100, True, meta=meta,
                         proof=[{"engine": "cvc5", "method": res.method,
                                 "goal": ex.get("goal"), "inductionVar": ex.get("inductionVar")}],
                         feedback="Certified: cvc5 proved ∀n. P(n) by structural induction"
                                  + (" (independently re-checked by Carcara)."
                                     if res.method == "alethe+carcara" else "."))
    if res.outcome == "proven_unequal":
        return _envelope("proven_unequal", 0, False, witness=res.witness, meta=meta,
                         feedback=f"Disproved: cvc5 found a counterexample {res.witness}.")
    if res.outcome == "equal_no_certificate":
        return _envelope("equal_no_certificate", None, False, meta=meta,
                         feedback="cvc5 proved the goal but no independently re-checked "
                                  "certificate is available; route to review.")
    # unknown: outside the fragment, timeout, refuted-without-witness, or no cvc5.
    reason = {"unavailable": "the cvc5 toolchain is unavailable in this deployment",
              "untranslatable": f"the goal is outside the supported fragment ({res.detail})",
              "rejected": "cvc5 did not settle the goal within the time budget"}.get(
                  res.method, res.detail)
    return _envelope("unknown", None, False, meta=meta,
                     feedback=f"cvc5regate could not certify this induction: {reason}. "
                              "Route to review.")


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
