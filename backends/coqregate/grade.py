from __future__ import annotations

import json
import sys
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

import coq_induction
import coq_prover

PROTOCOL = "1.0"
BACKEND = "coqregate"
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

    # Induction is exactly where a formal backend earns its keep. We GRADE THE
    # STUDENT'S derivation, not just the bare theorem: each submitted step becomes
    # a Coq-checked equality (the inductive step under the IH). A fabricated step
    # is `invalid_derivation`; both obligations reducing to `t = t` certify the
    # induction. A missing/half-empty submission is `unknown` (route to review) —
    # never an auto-pass on a true theorem the student did not prove. (The bare
    # theorem certifier, `coq_induction.certify`, remains for the authoring-time
    # "is this exercise certifiable?" oracle, but never stands in as a grade.)
    if ex.get("mode") == "induction":
        sub = request.get("submission") or {}
        res = coq_induction.grade_derivation(ex, sub)
        meta = {"induction": {"var": ex.get("inductionVar"),
                              "status": res.status, "reason": res.reason}}
        if res.status == "certified":
            return _envelope("proven_equal", 100, True, meta=meta,
                             feedback="Certified: every step of your base case and inductive "
                                      "step is Coq-checked; ∀n. P(n) follows by induction.")
        if res.status == "invalid":
            return _envelope("invalid_derivation", 0, False, meta=meta,
                             feedback=f"Invalid induction proof: {res.reason}.")
        reason = {
            "unattempted": "no derivation submitted to grade",
            "unavailable": "the Coq toolchain is unavailable in this deployment",
            "untranslatable": f"the goal is outside the gradeable fragment ({res.reason})",
        }.get(res.status, res.reason)
        return _envelope("unknown", None, False, meta=meta,
                         feedback=f"Coqregate could not grade this induction: {reason}. "
                                  f"Route to review.")

    # Coqregate is an induction specialist; everything else is out of scope.
    if "source" not in ex and ex.get("goal") is None:
        raise RequestError("exercise.source (or, for induction, exercise.goal) is required")
    return _envelope("unknown", None, False,
                     feedback="Coqregate only certifies induction proofs (mode: 'induction'); "
                              "use the Eggregate or Leanregate backend for equational grading.")


# ---- transports (mirror Leanregate's grade.py / Eggregate's server.py) ------
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
                             "coq_available": coq_prover.coq_available()})
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
