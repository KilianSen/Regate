"""Transports for the grading protocol -- one handler, two entrypoints.

    python -m eggregate.server            # HTTP: POST /grade, GET /health  (port 8000)
    python -m eggregate.server --cli      # CLI:  GradeRequest stdin -> GradeResponse stdout

Both call ``service.grade``.  Stdlib only (no framework) so the OCI image is
small and the egglog wheel is the only non-trivial dependency.
"""
from __future__ import annotations

import json
import sys
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer

from .service import BACKEND, PROTOCOL, VERSION, RequestError, grade


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
    def _send(self, code: int, body: dict):
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
        except Exception as e:                       # never leak a stack trace as a grade
            self._send(500, {"error": f"internal error: {type(e).__name__}"})

    def log_message(self, *args):                    # quiet by default
        pass


def run_http(host: str = "0.0.0.0", port: int = 8000) -> int:
    server = ThreadingHTTPServer((host, port), _Handler)
    sys.stderr.write(f"{BACKEND} {VERSION} (protocol {PROTOCOL}) on http://{host}:{port}\n")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    return 0


if __name__ == "__main__":
    if "--cli" in sys.argv:
        raise SystemExit(run_cli())
    port = 8000
    if "--port" in sys.argv:
        port = int(sys.argv[sys.argv.index("--port") + 1])
    raise SystemExit(run_http(port=port))
