# Eggregate grading backend — build from the MONOREPO ROOT as context:
#   docker build -f backends/eggregate/Dockerfile -t eggregate .
#
# Stable CPython 3.13 + the OFFICIAL egglog wheel (the patched 3.15t build in
# docs/BUILD-egglog-3.15t.md was for experiments only).
FROM python:3.13-slim

WORKDIR /app
RUN pip install --no-cache-dir "egglog==13.2.0"

COPY backends/eggregate/eggregate ./eggregate
COPY GRADING_PROTOCOL.md ./

EXPOSE 8000
# HTTP by default; pass "--cli" for per-submission batch grading.
ENTRYPOINT ["python", "-m", "eggregate.server"]
