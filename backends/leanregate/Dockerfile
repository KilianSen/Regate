# Leanregate grading backend — build from the MONOREPO ROOT as context:
#   docker build -f backends/leanregate/Dockerfile -t leanregate .
#
# The grading entrypoint (grade.py) is stdlib-only Python, so the deployable
# image is tiny. Compiling/checking the verified rule library
# (backends/leanregate/Leanregate/Basic.lean) needs the Lean toolchain + Mathlib
# (`lake build`); once the Lean step-checker is wired into grade.py, add a Lean
# build stage here.
FROM python:3.13-slim

WORKDIR /app
COPY backends/leanregate/grade.py ./
COPY GRADING_PROTOCOL.md ./

EXPOSE 8000
ENTRYPOINT ["python", "grade.py"]
