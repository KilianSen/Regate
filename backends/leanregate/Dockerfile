# Leanregate grading backend — build from the MONOREPO ROOT as context:
#   docker build -f backends/leanregate/Dockerfile -t leanregate .
#
# Two stages. The `lean` stage carries the Lean toolchain + Mathlib so the
# *runtime* prover (lean_prover.py) can establish soundness of a transmitted
# `exercise.ruleset` at request time — trusted authors ship rules on the wire and
# the kernel proves each one (hybrid ring/field_simp + proof-carrying). The
# runtime stage copies that toolchain plus the stdlib-only grading entrypoint.
#
# NOTE: this image carries Mathlib oleans and is built in CI / the registry, not
# in the scaffold env. It is slimmed to the transitive closure of the runtime
# import surface (`Mathlib.Tactic` + `Rat.Defs`) by prune_lake.py — the full
# Mathlib olean set is never shipped. Without the toolchain the Python CLI still
# runs and degrades honestly: an inline ruleset returns `unknown`
# (lean_prover.lean_available() is False), never a false grade.

# ---- stage 1: Lean toolchain + Mathlib oleans -----------------------------
FROM python:3.13-slim AS lean
ENV ELAN_HOME=/opt/elan PATH=/opt/elan/bin:$PATH
RUN apt-get update && apt-get install -y --no-install-recommends \
        curl git ca-certificates && rm -rf /var/lib/apt/lists/*

WORKDIR /app/leanproj
COPY backends/leanregate/lakefile.toml backends/leanregate/lean-toolchain ./

# elan installs the lean/lake version pinned by lean-toolchain; lake then fetches
# Mathlib's *prebuilt* oleans (`cache get`) instead of compiling from scratch.
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
        | sh -s -- -y --no-modify-path \
    && elan toolchain install "$(cat lean-toolchain)" \
    && elan default "$(cat lean-toolchain)" \
    && lake update \
    && lake exe cache get

# Warm the prover's import set so the first request is not a cold elaboration.
RUN mkdir -p Regate \
    && printf 'import Mathlib.Tactic.Ring\nimport Mathlib.Tactic.FieldSimp\n' > Regate/Warm.lean \
    && lake env lean Regate/Warm.lean

# Bake `lake env`'s search paths so the RUNTIME can call `lean` directly and never
# touch `lake` (lake env re-resolves deps and re-clones packages from GitHub if a
# checkout looks off, wiping the oleans). lean_prover reads this file; with it the
# .git clones are no longer needed at runtime, so prune_lake drops them.
RUN cd /app/leanproj \
    && { printf 'LEAN_PATH=%s\n' "$(lake env printenv LEAN_PATH)"; \
         printf 'LD_LIBRARY_PATH=%s\n' "$(lake env printenv LD_LIBRARY_PATH)"; } \
       > /app/leanproj/.lean_env

ENV LEANREGATE_LEAN_PROJECT=/app/leanproj
COPY backends/leanregate/lean_prover.py backends/leanregate/lean_induction.py \
     backends/leanregate/check_induction.py backends/leanregate/prune_lake.py ./

# Slim the cache: `cache get` pulls ALL Mathlib oleans, but the runtime only
# elaborates the `Mathlib.Tactic` + `Rat.Defs` surface. Delete every olean Lean
# does not load for that surface (it enumerates them via findOLean), plus
# .git/.ilean/widget JS. prune_lake self-verifies the auto-prove path afterwards
# (via `lean` direct, using the baked .lean_env).
RUN python prune_lake.py \
    && rm -rf "$ELAN_HOME"/toolchains/*/share/doc

# Gate the image on the induction translator AFTER pruning, so this kernel-check
# also proves the slimmed olean set still elaborates the induction import surface.
# A regressed emitter OR an over-aggressive prune fails the build here.
RUN python check_induction.py --require-lean

# ---- stage 2: runtime -----------------------------------------------------
FROM python:3.13-slim
ENV ELAN_HOME=/opt/elan PATH=/opt/elan/bin:$PATH \
    LEANREGATE_LEAN_PROJECT=/app/leanproj
RUN apt-get update && apt-get install -y --no-install-recommends \
        git ca-certificates && rm -rf /var/lib/apt/lists/*

COPY --from=lean /opt/elan /opt/elan
COPY --from=lean /app/leanproj /app/leanproj

WORKDIR /app
COPY backends/leanregate/grade.py backends/leanregate/lean_check.py \
     backends/leanregate/lean_prover.py backends/leanregate/lean_induction.py ./
COPY GRADING_PROTOCOL.md ./

EXPOSE 8000
ENTRYPOINT ["python", "grade.py"]
