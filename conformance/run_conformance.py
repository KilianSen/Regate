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
import shutil
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
    # Certifier backends — only exercised by fixtures that carry an
    # `expect.coqregate` / `expect.cvc5regate`. Their verdict on a *correct*
    # induction is toolchain-dependent (`proven_equal` with coqc/cvc5 present,
    # `unknown` without), so gate any such fixture on the tool being installed.
    "coqregate": {
        "cmd": os.environ.get("COQREGATE_CMD",
                              f"{sys.executable} {ROOT}/backends/coqregate/grade.py --cli"),
        "cwd": ROOT,
    },
    "cvc5regate": {
        "cmd": os.environ.get("CVC5REGATE_CMD",
                              f"{sys.executable} {ROOT}/backends/cvc5regate/grade.py --cli"),
        "cwd": ROOT,
    },
}

ENVELOPE = ("protocol", "backend", "outcome", "score", "certified")
OUTCOMES = {"proven_equal", "proven_unequal", "equal_no_certificate",
            "invalid_derivation", "unknown"}


_PROBE_CACHE: dict[str, bool] = {}


def toolchain_present(name: str) -> bool:
    """Is the prover a fixture needs actually usable here?

    ``lean`` is special: the binary on PATH is not enough, the backend also needs a
    prebuilt Mathlib project, so we ask the backend's own predicate rather than
    guessing. Everything else is a plain executable lookup.
    """
    if name in _PROBE_CACHE:
        return _PROBE_CACHE[name]
    if name == "lean":
        probe = subprocess.run(
            [sys.executable, "-c", "import lean_prover; print(lean_prover.lean_available())"],
            capture_output=True, text=True, cwd=ROOT / "backends" / "leanregate")
        ok = probe.stdout.strip() == "True"
    else:
        ok = shutil.which(name) is not None
    _PROBE_CACHE[name] = ok
    return ok


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
    if "certified" in expect and resp.get("certified") != expect["certified"]:
        fails.append(f"certified {resp.get('certified')!r} != {expect['certified']!r}")
    if expect.get("has_witness") and not resp.get("witness"):
        fails.append("expected a witness, none present")
    if expect.get("has_proof") and not resp.get("proof"):
        fails.append("expected a proof, none present")
    if expect.get("has_hint") and not resp.get("hint"):
        fails.append("expected a hint, none present")
    # Protocol invariants, checked on every response regardless of what the fixture
    # asserts: `certified: true` owes a re-checkable proof, and `proven_unequal`
    # owes a witness. Both were violated in practice before these were enforced.
    # An *empty* proof is a valid zero-step certificate ("already the target form"),
    # so the test is `is None`, not falsiness.
    if (resp.get("certified") and resp.get("outcome") == "proven_equal"
            and resp.get("proof") is None):
        fails.append("certified: true with no proof (protocol violation)")
    if resp.get("outcome") == "proven_unequal" and not resp.get("witness"):
        fails.append("proven_unequal with no witness (protocol violation)")
    return fails


def main() -> int:
    total = passed = skipped = 0
    for path in FIXTURES:
        fx = json.loads(path.read_text())
        for backend, expect in fx["expect"].items():
            # A fixture may declare `"requires": "coqc"`: the certifier backends give
            # a toolchain-dependent verdict, so without the tool the check is not run
            # rather than silently asserting the degraded `unknown`.
            need = expect.get("requires")
            if need and not toolchain_present(need):
                skipped += 1
                print(f"  skip {fx['name']:<24} [{backend}]  -> {need} not available")
                continue
            total += 1
            fails = check(backend, fx["request"], expect)
            mark = "ok  " if not fails else "FAIL"
            passed += not fails
            print(f"  {mark} {fx['name']:<24} [{backend}]"
                  + ("" if not fails else "  -> " + "; ".join(fails)))
    tail = f" ({skipped} skipped: toolchain absent)" if skipped else ""
    print(f"\n{passed}/{total} conformance checks passed{tail}")
    return 0 if passed == total else 1


if __name__ == "__main__":
    raise SystemExit(main())
