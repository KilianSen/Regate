#!/usr/bin/env python3
"""Protocol conformance harness — the monorepo's reason to exist.

Pipes every fixture in `fixtures/` through each backend's CLI transport and
checks: (a) the response is a valid protocol envelope (or a well-formed error),
and (b) the per-backend expectations hold. This is what proves Eggregate and
Leanregate implement the *same* contract — change either backend, and a protocol
regression fails here.

    python conformance/run_conformance.py

Backend commands are configurable via env vars (defaults assume a local checkout):
    EGGREGATE_CMD   default: python -m eggregate.server --cli   (run in backends/eggregate)
    LEANREGATE_CMD  default: python backends/leanregate/grade.py --cli
"""
from __future__ import annotations

import json
import os
import shlex
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FIXTURES = sorted((ROOT / "conformance" / "fixtures").glob("*.json"))

BACKENDS = {
    "eggregate": {
        "cmd": os.environ.get("EGGREGATE_CMD",
                              f"{sys.executable} -m eggregate.server --cli"),
        "cwd": ROOT / "backends" / "eggregate",
    },
    "leanregate": {
        "cmd": os.environ.get("LEANREGATE_CMD",
                              f"{sys.executable} {ROOT}/backends/leanregate/grade.py --cli"),
        "cwd": ROOT,
    },
}

ENVELOPE = ("protocol", "backend", "outcome", "score", "certified")
OUTCOMES = {"proven_equal", "proven_unequal", "equal_no_certificate",
            "invalid_derivation", "unknown"}


def invoke(backend: str, request: dict) -> dict:
    b = BACKENDS[backend]
    p = subprocess.run(shlex.split(b["cmd"]), input=json.dumps(request),
                       capture_output=True, text=True, cwd=b["cwd"])
    try:
        return json.loads(p.stdout)
    except json.JSONDecodeError:
        return {"error": f"non-JSON output (exit {p.returncode}): {p.stderr[:200]}"}


def check(backend: str, request: dict, expect: dict) -> list[str]:
    resp = invoke(backend, request)
    fails = []
    if expect.get("error"):
        if "error" not in resp:
            fails.append(f"expected an error, got {resp.get('outcome')}")
        return fails
    if "error" in resp:
        return [f"unexpected error: {resp['error']}"]
    for field in ENVELOPE:                      # valid envelope
        if field not in resp:
            fails.append(f"missing envelope field {field!r}")
    if resp.get("outcome") not in OUTCOMES:
        fails.append(f"bad outcome {resp.get('outcome')!r}")
    if "outcome" in expect and resp.get("outcome") != expect["outcome"]:
        fails.append(f"outcome {resp.get('outcome')!r} != {expect['outcome']!r}")
    if "score" in expect and resp.get("score") != expect["score"]:
        fails.append(f"score {resp.get('score')!r} != {expect['score']!r}")
    if expect.get("has_witness") and not resp.get("witness"):
        fails.append("expected a witness, none present")
    return fails


def main() -> int:
    total = passed = 0
    for path in FIXTURES:
        fx = json.loads(path.read_text())
        for backend, expect in fx["expect"].items():
            total += 1
            fails = check(backend, fx["request"], expect)
            mark = "ok  " if not fails else "FAIL"
            passed += not fails
            print(f"  {mark} {fx['name']:<24} [{backend}]"
                  + ("" if not fails else "  -> " + "; ".join(fails)))
    print(f"\n{passed}/{total} conformance checks passed")
    return 0 if passed == total else 1


if __name__ == "__main__":
    raise SystemExit(main())
