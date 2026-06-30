from __future__ import annotations

import hashlib
import os
import shutil
import subprocess
import tempfile

# Cold-start of `coqc` on a small QArith file is sub-second, but allow generous
# headroom for a loaded machine / first run. Override with COQREGATE_COQ_TIMEOUT.
COQ_TIMEOUT = float(os.environ.get("COQREGATE_COQ_TIMEOUT", "60"))


# ---------------------------------------------------------------------------
# Toolchain discovery.
# ---------------------------------------------------------------------------
def _coq_cmd(src_path: str) -> list[str] | None:
    """The argv that compiles `src_path`, or None if no toolchain is present.

    `coqc` is the classic binary (Coq 8.x and the Rocq 9.x compatibility
    symlink); `rocq compile` is the Rocq 9.x spelling. We silence the
    stdlib-prefix deprecation warnings so a clean compile produces no stderr."""
    warn = "-w"
    warn_spec = "-deprecated-from-Coq,-deprecated-missing-stdlib"
    coqc = shutil.which("coqc")
    if coqc:
        return [coqc, warn, warn_spec, src_path]
    rocq = shutil.which("rocq")
    if rocq:
        return [rocq, "compile", warn, warn_spec, src_path]
    return None


def coq_available() -> bool:
    """True iff a Coq/Rocq compiler is on PATH."""
    return shutil.which("coqc") is not None or shutil.which("rocq") is not None


# ---------------------------------------------------------------------------
# The compile seam (the only thing that touches the toolchain).
# ---------------------------------------------------------------------------
def _run_coq(source: str) -> tuple[bool, str]:
    """Compile `source` with coqc/rocq. (True, "") on success; (False, detail)
    on a Coq error, missing toolchain, or timeout.

    Isolated so tests can stub it without a Coq install."""
    if not coq_available():
        return False, "coq toolchain unavailable"
    # coqc writes a sibling `.vo` (and `.glob`/`.vos`…); use a scratch dir so we
    # never litter the project and cleanup is a single rmtree.
    tmp = tempfile.mkdtemp(prefix="coqregate-")
    src = os.path.join(tmp, "Check.v")
    try:
        with open(src, "w", encoding="utf-8") as fh:
            fh.write(source)
        cmd = _coq_cmd(src)
        if cmd is None:                       # raced against PATH change
            return False, "coq toolchain unavailable"
        try:
            proc = subprocess.run(
                cmd, capture_output=True, text=True, timeout=COQ_TIMEOUT,
            )
        except subprocess.TimeoutExpired:
            return False, f"coq timed out after {COQ_TIMEOUT}s"
        if proc.returncode == 0:
            return True, ""
        return False, (proc.stderr or proc.stdout or "coq error").strip()
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


# ---------------------------------------------------------------------------
# Content-addressed cache (same style as lean_prover).
# ---------------------------------------------------------------------------
_CACHE: dict[str, tuple[bool, str]] = {}


def check_source(source: str) -> tuple[bool, str]:
    """`_run_coq` with a per-source-hash cache: identical source ⇒ same outcome."""
    key = hashlib.sha256(source.encode()).hexdigest()
    cached = _CACHE.get(key)
    if cached is not None:
        return cached
    result = _run_coq(source)
    _CACHE[key] = result
    return result
