"""Leanregate grading entrypoint — conforms to the shared grading protocol.

    python grade.py            # HTTP: POST /grade, GET /health  (port 8000)
    python grade.py --cli      # CLI:  GradeRequest stdin -> GradeResponse stdout

Self-contained (stdlib only); shares no code with Eggregate — it shares only the
*protocol* (GRADING_PROTOCOL.md), which is the point. Until the Lean step-checker
that consumes `Leanregate/Basic.lean` is wired in, this grades the *decidable*
part (reaching the target form) and returns `unknown` wherever a Lean proof is
required — honestly inconclusive, never a false grade.
"""
from __future__ import annotations

import json
import sys
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

PROTOCOL = "1.0"
BACKEND = "leanregate"
VERSION = "0.0.1"


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
    if "source" not in ex:
        raise RequestError("exercise.source is required")
    if ex.get("mode", "transformation") == "transformation" and ex.get("target") is None:
        raise RequestError("transformation mode requires exercise.target")
    if sub.get("final") is None and not sub.get("steps"):
        raise RequestError("submission must have a final expression or steps")

    target = ex.get("target")

    # A formal backend may only use rules it has a proof for. Inline
    # instructor-authored rules (`ruleset`) would each need a Lean proof, which
    # the scaffold does not have yet -> it cannot soundly grade derivations under
    # them. (Built-in `rules` ids map to lemmas in Basic.lean once wired.)
    if ex.get("ruleset"):
        return _envelope("unknown", None, False,
                         feedback="Leanregate requires a Lean proof per rule; "
                                  "inline custom rulesets are not yet supported. "
                                  "Use built-in rule ids or the Eggregate backend.")

    # Decidable without any rule: a final expression that *is* the target form is
    # correct regardless of path (structural equality on canonical MathNode JSON).
    if sub.get("final") is not None and target is not None:
        if sub["final"] == target:
            return _envelope("proven_equal", 100, True,
                             feedback="Reached the target form.")

    # Everything else — value-equivalence, partial credit, and formal step
    # validity — needs the Lean checker (Basic.lean), not yet wired.
    return _envelope("unknown", None, False,
                     feedback="Leanregate scaffold: formal verification of "
                              "equivalence/derivations is not yet wired; route to "
                              "review or use the Eggregate backend.")


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
