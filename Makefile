# Regate monorepo — common tasks. Uses uv for the Python env (egglog needs a
# stable CPython 3.11-3.13). Override PY to use an existing interpreter.
PY ?= .venv/bin/python

.PHONY: setup test gate conformance lean docker up ci clean

setup:                ## create venv and install the eggregate backend (+egglog)
	uv venv --python 3.13 .venv
	uv pip install --python $(PY) -e backends/eggregate

test:                 ## eggregate test suite
	$(PY) backends/eggregate/tests/test_eggregate.py

gate:                 ## rule-library soundness gate (non-zero on an unsound rule)
	cd backends/eggregate && $(abspath $(PY)) check_rules.py

conformance:          ## run every fixture through BOTH backends' CLIs
	$(PY) conformance/run_conformance.py

lean:                 ## build & check the Lean verified rule library
	cd backends/leanregate && lake build

docker:               ## build both backend images (context = repo root)
	docker build -f backends/eggregate/Dockerfile -t eggregate .
	docker build -f backends/leanregate/Dockerfile -t leanregate .

up:                   ## run both backends via docker compose
	docker compose up --build

ci: test gate conformance   ## what CI runs

clean:
	rm -rf .venv backends/eggregate/eggregate/__pycache__ \
	       backends/eggregate/tests/__pycache__ backends/leanregate/.lake
