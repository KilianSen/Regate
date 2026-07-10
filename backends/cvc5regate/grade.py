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
        return _grade_induction(ex, request.get("submission") or {})

    # cvc5regate is an induction certifier. Equational derivations / endpoint
    # equivalence are graded by eggregate (e-graph) or leanregate (formal); this
    # backend is honestly inconclusive on them rather than guessing.
    if "goal" not in ex and "source" not in ex:
        raise RequestError("exercise must have a 'goal' (induction) or 'source'")
    return _envelope("unknown", None, False,
                     feedback="cvc5regate certifies inductive goals (mode='induction'); "
                              "equational derivations are out of scope — use the "
                              "eggregate or leanregate backend, or route to review.")


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
