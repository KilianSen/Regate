# Coqregate grading backend — build from the MONOREPO ROOT as context:
#   docker build -f backends/coqregate/Dockerfile -t coqregate .
#
# A *certifier* backend like leanregate, but ~10x lighter: it emits a Coq
# `induction` proof for the transmitted goal + recursive definitions and
# kernel-checks it with `coqc`. Coq's `ring`/`field`/`lia` ship in the standard
# library, so there is NO Mathlib-scale dependency — the whole toolchain is a
# few hundred MB and fully offline. Without `coqc` the Python CLI still runs and
# degrades honestly to `unknown` (coq_prover.coq_available() is False), never a
# false grade.
FROM python:3.13-slim

# `coq` from Debian pulls the coqc kernel + the standard library (ring/field/lia).
RUN apt-get update && apt-get install -y --no-install-recommends \
        coq && rm -rf /var/lib/apt/lists/*

WORKDIR /app
COPY backends/coqregate/grade.py backends/coqregate/coq_induction.py \
     backends/coqregate/coq_prover.py backends/coqregate/step_check.py ./
COPY GRADING_PROTOCOL.md ./

EXPOSE 8000
# HTTP by default; pass "--cli" for per-submission batch grading.
ENTRYPOINT ["python", "grade.py"]
