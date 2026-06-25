# egglog on free-threaded CPython 3.15t

The stock `egglog` (13.2.0) has **no wheel for Python 3.15**, and its sdist
won't build there: it pins **PyO3 0.27**, which maxes out at Python 3.14.
On free-threaded CPython the usual `PYO3_USE_ABI3_FORWARD_COMPATIBILITY=1`
override does *not* work, because the free-threaded build has no limited/stable
ABI. So the only path is to build against a newer PyO3.

This repo vendors a working patched build:

- `vendor/egglog-13.2.0-cp315-cp315t-macosx_11_0_arm64.whl` — installable wheel
- `vendor/egglog-src-patched/` — the patched sdist used to produce it

## Install (already done in `.venv`)

```sh
uv venv --python 3.15.0b2+freethreaded .venv --allow-existing
uv pip install --python .venv/bin/python vendor/egglog-13.2.0-cp315-cp315t-macosx_11_0_arm64.whl
```

## How the wheel was built (to reproduce / re-patch)

Requires Rust (`rustup`/`cargo`) and `uv`.

1. Get egglog's sdist source (or use `vendor/egglog-src-patched/`).
2. In `Cargo.toml`, bump the PyO3 pin: `pyo3 = { version = "0.27" ... }` -> `"0.29"`.
3. Update **only** PyO3 in the lockfile (keep the pinned egglog Rust crates):
   ```sh
   cargo update -p pyo3 --precise 0.29.0
   ```
   (Do NOT delete `Cargo.lock` — that pulls newer egglog Rust crates whose
   trait API has drifted and produces ~20 unrelated errors.)
4. PyO3 0.29 tightened `call1`'s bounds. In `src/py_object_sort.rs`:
   ```rust
   // before
   pub fn dump<X>(obj: Bound<X>) -> PyResult<PyPickledValue> {
   // after
   pub fn dump<X: pyo3::PyTypeInfo>(obj: Bound<X>) -> PyResult<PyPickledValue> {
   ```
5. Build:
   ```sh
   python -m maturin build --release -i /path/to/.venv/bin/python
   # -> target/wheels/egglog-13.2.0-cp315-cp315t-macosx_11_0_arm64.whl
   ```

## Caveats

- Unofficial build against a CPython **beta** (3.15.0b2), not validated against
  egglog's test suite on free-threaded. Imports + equality saturation verified;
  treat real multi-threaded concurrency as unproven (PyO3 0.29 + the egglog Rust
  crates' thread-safety on free-threaded is not upstream-tested).
- Pinned to this exact wheel. Any `egglog` version bump reintroduces the problem.
- A stable fallback: `uv venv --python 3.13 .venv` + `uv pip install egglog`
  uses the official wheel and Just Works.
