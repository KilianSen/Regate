from __future__ import annotations

import os
import shutil
import subprocess
import sys

PROJECT = os.environ.get("LEANREGATE_LEAN_PROJECT", "/app/leanproj")
PACKAGES = os.path.join(PROJECT, ".lake", "packages")

# The exact import surface the runtime ever elaborates (superset of every path:
# lean_prover._auto_source and lean_induction). MUST stay ⊇ the imports those
# emit; over-keeping is safe, under-keeping breaks the image.
RUNTIME_IMPORTS = [
    "import Mathlib.Tactic",
    "import Mathlib.Data.Rat.Defs",
    "import Mathlib.Tactic.Ring",
    "import Mathlib.Tactic.FieldSimp",
]
# Mathlib.Tactic's closure is several thousand modules; refuse to prune if we got
# far fewer (⇒ Lean errored), rather than delete against a half-empty keep-set.
MIN_CLOSURE = 1500


def _real(p: str) -> str:
    return os.path.realpath(p)


def closure_olean_paths() -> set[str]:
    """The exact olean files Lean loads for the runtime surface, as realpaths.

    Asks Lean to resolve every transitively-imported module to its olean via
    `findOLean`, so the keep-set is file paths Lean itself reports — no
    assumption about where the build put the oleans."""
    src_dir = os.path.join(PROJECT, "Regate")
    os.makedirs(src_dir, exist_ok=True)
    src = os.path.join(src_dir, "Closure.lean")
    body = (
        "\n".join(RUNTIME_IMPORTS) + "\n\n"
        "open Lean in\n"
        "run_cmd do\n"
        "  for m in (← getEnv).header.moduleNames do\n"
        "    IO.println (← Lean.findOLean m)\n"
    )
    with open(src, "w", encoding="utf-8") as fh:
        fh.write(body)
    proc = subprocess.run(
        ["lake", "env", "lean", os.path.relpath(src, PROJECT)],
        cwd=PROJECT, capture_output=True, text=True, timeout=900,
    )
    if proc.returncode != 0:
        sys.exit("prune_lake: Lean failed to enumerate the runtime closure:\n"
                 + (proc.stderr or proc.stdout))
    paths = set()
    for ln in proc.stdout.splitlines():
        ln = ln.strip()
        if ln.endswith(".olean") and os.path.exists(ln):
            paths.add(_real(ln))
    return paths


def _du(path: str) -> int:
    total = 0
    for root, _dirs, files in os.walk(path):
        for f in files:
            try:
                total += os.path.getsize(os.path.join(root, f))
            except OSError:
                pass
    return total


def _self_verify() -> None:
    """Re-prove a known-sound rule through the real prover after pruning.
    `a + b = b + a` exercises the auto-prove path (`import Mathlib.Tactic.Ring`
    /`FieldSimp`); if the prune broke that import, this fails the build."""
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import lean_prover
    lean_prover.LEAN_TIMEOUT = float(os.environ.get("LEANREGATE_SELFTEST_TIMEOUT", "600"))
    wild = lambda v: {"type": "wild", "value": v}
    add = lambda l, r: {"type": "add", "slots": {"left": [l], "right": [r]}}
    rule = {"id": "_prune_selftest_add_comm",
            "lhs": add(wild("a"), wild("b")), "rhs": add(wild("b"), wild("a")),
            "conditions": []}
    res = lean_prover.prove_rule(rule)
    if not res.proven:
        sys.exit("prune_lake: POST-PRUNE SELF-TEST FAILED — the prover can no "
                 f"longer prove a+b=b+a (method={res.method}); the prune removed "
                 f"a needed olean.\n{res.detail}")
    print(f"prune_lake: self-verify OK (auto-proved a+b=b+a via {res.method})")


def main() -> None:
    if not os.path.isdir(PACKAGES):
        sys.exit(f"prune_lake: no packages dir at {PACKAGES}")
    before = _du(PROJECT)

    keep = closure_olean_paths()
    if len(keep) < MIN_CLOSURE:
        sys.exit(f"prune_lake: closure has only {len(keep)} oleans "
                 f"(< {MIN_CLOSURE}); refusing to prune.")
    print(f"prune_lake: runtime closure = {len(keep)} oleans")

    # Tier 2: delete every package olean (+ sibling .ilean) Lean did not load.
    dead = freed = 0
    for root, _dirs, files in os.walk(PACKAGES):
        for f in files:
            if not f.endswith(".olean"):
                continue
            full = os.path.join(root, f)
            if _real(full) in keep:
                continue
            for victim in (full, full[:-len(".olean")] + ".ilean"):
                if os.path.exists(victim):
                    freed += os.path.getsize(victim)
                    os.remove(victim)
            dead += 1
    print(f"prune_lake: removed {dead} dead oleans")

    # Tier 1: .ilean (language-server only), ProofWidgets JS, and — only when the
    # runtime will call `lean` directly (the .lean_env is baked, so lake never runs
    # at runtime) — the package .git clones (~1.2 GB). We must NOT drop .git when
    # lake is the runtime engine: `lake env` verifies each dependency's checkout
    # against its git remote and, with .git gone, reports "URL has changed" and
    # re-clones it — wiping the oleans and needing network. The self-verify below
    # runs through `lean` direct, so a wrong call here fails the build.
    drop_git = os.path.isfile(os.path.join(PROJECT, ".lean_env"))
    removed_ilean = removed_git = 0
    for root, dirs, files in os.walk(PACKAGES, topdown=True):
        if drop_git and ".git" in dirs:
            shutil.rmtree(os.path.join(root, ".git"), ignore_errors=True)
            dirs.remove(".git")
            removed_git += 1
        for f in files:
            if f.endswith(".ilean"):
                try:
                    os.remove(os.path.join(root, f)); removed_ilean += 1
                except OSError:
                    pass
    pw_js = os.path.join(PACKAGES, "proofwidgets", ".lake", "build", "js")
    removed_js = 0
    if os.path.isdir(pw_js):
        removed_js = _du(pw_js)
        shutil.rmtree(pw_js, ignore_errors=True)
    print(f"prune_lake: removed {removed_git} .git, {removed_ilean} .ilean, "
          f"{removed_js // (1024*1024)} MiB ProofWidgets JS "
          f"({'lean-direct' if drop_git else 'kept .git for lake'})")

    after = _du(PROJECT)
    print(f"prune_lake: {before // (1024*1024)} MiB -> {after // (1024*1024)} MiB "
          f"(freed {(before - after) // (1024*1024)} MiB)")

    _self_verify()


if __name__ == "__main__":
    main()
