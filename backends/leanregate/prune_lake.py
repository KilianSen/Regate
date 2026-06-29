"""Build-time image slimmer for the Lean stage (NOT shipped to runtime).

`lake exe cache get` downloads the oleans for *all* of Mathlib (~5 GB), but the
container only ever elaborates the runtime-generated files in `lean_prover` /
`lean_induction`, whose import surface is `Mathlib.Tactic` + `Mathlib.Data.Rat.Defs`
(see `_carried_source`). Lean loads exactly the transitive closure of those
imports and nothing else, so every olean outside that closure is dead weight.

This script:

  1. asks Lean itself for the authoritative transitive module set of the runtime
     import surface (`#eval … moduleNames`) — no heuristics, no guessing;
  2. deletes every package olean whose module is not in that set (Tier 2);
  3. drops `.git` clones, `.ilean` server indices, and ProofWidgets' JS bundles,
     none of which headless `lake env lean` reads (Tier 1).

It ABORTS without deleting anything if the closure looks implausibly small, so a
Lean error can never nuke the build cache. stdlib-only.
"""
from __future__ import annotations

import os
import re
import subprocess
import sys

PROJECT = os.environ.get("LEANREGATE_LEAN_PROJECT", "/app/leanproj")
PACKAGES = os.path.join(PROJECT, ".lake", "packages")
LIB_MARKER = "/.lake/build/lib/"

# The exact import surface the runtime ever elaborates (superset of every path:
# _carried_source, _auto_source, lean_induction, Basic.lean).
RUNTIME_IMPORTS = [
    "import Mathlib.Tactic",
    "import Mathlib.Data.Rat.Defs",
    "import Mathlib.Tactic.Ring",
    "import Mathlib.Tactic.FieldSimp",
]
# Mathlib.Tactic's closure is many thousands of modules; refuse to prune if we
# somehow got far fewer (⇒ Lean errored), rather than delete a half-empty set.
MIN_CLOSURE = 1500

_NAME_RE = re.compile(r"^[A-Za-z0-9_.«».]+$")


def closure_modules() -> set[str]:
    """The transitive imported-module set of the runtime surface, per Lean."""
    src_dir = os.path.join(PROJECT, "Regate")
    os.makedirs(src_dir, exist_ok=True)
    src = os.path.join(src_dir, "Closure.lean")
    body = (
        "\n".join(RUNTIME_IMPORTS) + "\n\n"
        "open Lean Elab Command in\n"
        "run_cmd do\n"
        "  for m in (← getEnv).header.moduleNames do\n"
        "    IO.println m\n"
    )
    with open(src, "w", encoding="utf-8") as fh:
        fh.write(body)
    proc = subprocess.run(
        ["lake", "env", "lean", os.path.relpath(src, PROJECT)],
        cwd=PROJECT, capture_output=True, text=True, timeout=600,
    )
    if proc.returncode != 0:
        sys.exit("prune_lake: Lean failed to elaborate the runtime surface:\n"
                 + (proc.stderr or proc.stdout))
    mods = {ln.strip() for ln in proc.stdout.splitlines()
            if ln.strip() and _NAME_RE.match(ln.strip())}
    return mods


def _module_of(olean_path: str) -> str | None:
    i = olean_path.find(LIB_MARKER)
    if i < 0:
        return None
    rel = olean_path[i + len(LIB_MARKER):]
    return rel[:-len(".olean")].replace("/", ".") if rel.endswith(".olean") else None


def _du(path: str) -> int:
    total = 0
    for root, _dirs, files in os.walk(path):
        for f in files:
            try:
                total += os.path.getsize(os.path.join(root, f))
            except OSError:
                pass
    return total


def main() -> None:
    if not os.path.isdir(PACKAGES):
        sys.exit(f"prune_lake: no packages dir at {PACKAGES}")
    before = _du(PROJECT)

    keep = closure_modules()
    if len(keep) < MIN_CLOSURE:
        sys.exit(f"prune_lake: closure has only {len(keep)} modules "
                 f"(< {MIN_CLOSURE}); refusing to prune.")
    print(f"prune_lake: runtime closure = {len(keep)} modules")

    # Tier 2: delete oleans (and sibling .ilean) outside the closure.
    dead_oleans = freed_oleans = 0
    for root, _dirs, files in os.walk(PACKAGES):
        for f in files:
            if not f.endswith(".olean"):
                continue
            full = os.path.join(root, f)
            mod = _module_of(full)
            if mod is None or mod in keep:
                continue
            for victim in (full, full[:-len(".olean")] + ".ilean"):
                if os.path.exists(victim):
                    freed_oleans += os.path.getsize(victim)
                    os.remove(victim)
            dead_oleans += 1
    print(f"prune_lake: removed {dead_oleans} dead oleans")

    # Tier 1: remaining .ilean (server-only), .git clones, ProofWidgets JS.
    removed_ilean = removed_git = removed_js = 0
    for root, dirs, files in os.walk(PACKAGES, topdown=True):
        if ".git" in dirs:
            import shutil
            shutil.rmtree(os.path.join(root, ".git"), ignore_errors=True)
            dirs.remove(".git")
            removed_git += 1
        for f in files:
            if f.endswith(".ilean"):
                p = os.path.join(root, f)
                try:
                    os.remove(p); removed_ilean += 1
                except OSError:
                    pass
    pw_js = os.path.join(PACKAGES, "proofwidgets", ".lake", "build", "js")
    if os.path.isdir(pw_js):
        import shutil
        removed_js = _du(pw_js)
        shutil.rmtree(pw_js, ignore_errors=True)
    print(f"prune_lake: removed {removed_git} .git clones, "
          f"{removed_ilean} stray .ilean, {removed_js // (1024*1024)} MiB ProofWidgets JS")

    after = _du(PROJECT)
    print(f"prune_lake: {before // (1024*1024)} MiB -> {after // (1024*1024)} MiB "
          f"(freed {(before - after) // (1024*1024)} MiB)")


if __name__ == "__main__":
    main()
