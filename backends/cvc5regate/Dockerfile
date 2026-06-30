# Cvc5regate grading backend — build from the MONOREPO ROOT as context:
#   docker build -f backends/cvc5regate/Dockerfile -t cvc5regate .
#
# A *certifier* backend like leanregate, but ~400x lighter (a single ~21MB
# solver binary instead of Lean+Mathlib's ~9GB) and with BROADER coverage:
# cvc5's native structural induction (`--quant-ind`) also proves inequalities
# and divisibility goals that the Lean/Coq emitters do not cover. It disproves
# first (false goal -> `proven_unequal` + numeric witness), then proves.
#
# TRUST NOTE: a successful cvc5 `unsat` is currently trusted (cvc5 1.3.x cannot
# export Alethe proofs for induction, so the Carcara re-check is inert here) —
# closer to eggregate's oracle than Coq/Lean's kernel-rechecked certificate. The
# Alethe->Carcara re-check plumbing is built and activates automatically once a
# cvc5 release exports induction proofs. Without the cvc5 binary the Python CLI
# still runs and degrades honestly to `unknown`.
FROM python:3.13-slim

# Official static cvc5 release binary on PATH. Pin the version to the one the
# emitter was verified against; bump deliberately.
ARG CVC5_VERSION=1.3.4
RUN apt-get update && apt-get install -y --no-install-recommends \
        curl ca-certificates unzip && rm -rf /var/lib/apt/lists/* \
    && curl -sSfL \
        "https://github.com/cvc5/cvc5/releases/download/cvc5-${CVC5_VERSION}/cvc5-Linux-x86_64-static.zip" \
        -o /tmp/cvc5.zip \
    && unzip -j /tmp/cvc5.zip "*/bin/cvc5" -d /usr/local/bin \
    && chmod +x /usr/local/bin/cvc5 \
    && rm /tmp/cvc5.zip \
    && cvc5 --version

WORKDIR /app
COPY backends/cvc5regate/grade.py backends/cvc5regate/cvc5_induction.py \
     backends/cvc5regate/cvc5_prover.py ./
COPY GRADING_PROTOCOL.md ./

EXPOSE 8000
# HTTP by default; pass "--cli" for per-submission batch grading.
ENTRYPOINT ["python", "grade.py"]
