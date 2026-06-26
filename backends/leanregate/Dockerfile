# Leanregate grading backend — build from the MONOREPO ROOT as context:
#   docker build -f backends/leanregate/Dockerfile -t leanregate .
#
# The grading entrypoint (grade.py + lean_check.py) is stdlib-only Python, so the
# deployable image is tiny. The step-checker certifies derivations against the
# lemmas proven in backends/leanregate/Leanregate/Basic.lean; compiling that file
# to re-verify the rule library needs the Lean toolchain + Mathlib (`lake build`),
# which would be a separate build stage here.
FROM python:3.13-slim

WORKDIR /app
COPY backends/leanregate/grade.py backends/leanregate/lean_check.py ./
COPY GRADING_PROTOCOL.md ./

EXPOSE 8000
ENTRYPOINT ["python", "grade.py"]
