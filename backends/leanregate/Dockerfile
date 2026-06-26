# Leanregate grading backend — build from the MONOREPO ROOT as context:
#   docker build -f backends/leanregate/Dockerfile -t leanregate .
#
# Two stages. The `lean` stage carries the Lean toolchain + Mathlib so the
# *runtime* prover (lean_prover.py) can establish soundness of a transmitted
# `exercise.ruleset` at request time — trusted authors ship rules on the wire and
# the kernel proves each one (hybrid ring/field_simp + proof-carrying). The
# runtime stage copies that toolchain plus the stdlib-only grading entrypoint.
#
# NOTE: this image is large (Mathlib oleans) and is built in CI / the registry,
# not in the scaffold env. Without it the Python CLI still runs and degrades
# honestly: an inline ruleset returns `unknown` (lean_prover.lean_available()
# is False), never a false grade.

# ---- stage 1: Lean toolchain + Mathlib oleans -----------------------------
FROM python:3.13-slim AS lean
ENV ELAN_HOME=/opt/elan PATH=/opt/elan/bin:$PATH
RUN apt-get update && apt-get install -y --no-install-recommends \
        curl git ca-certificates && rm -rf /var/lib/apt/lists/*

WORKDIR /app/leanproj
COPY backends/leanregate/lakefile.toml backends/leanregate/lean-toolchain ./
COPY backends/leanregate/Leanregate ./Leanregate

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

# Gate the image on the induction translator: emit the proofs and kernel-check them
# here, where the toolchain already lives. A regressed emitter fails the build, so
# we never ship an image that generates broken Lean. (MUST_PASS asserts; harder
# goals are best-effort.)
ENV LEANREGATE_LEAN_PROJECT=/app/leanproj
COPY backends/leanregate/lean_prover.py backends/leanregate/lean_induction.py \
     backends/leanregate/check_induction.py ./
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
