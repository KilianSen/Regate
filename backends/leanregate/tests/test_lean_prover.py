"""Runtime-prover tests for Leanregate. The Lean toolchain is not present in the
test/scaffold env, so these stub the single subprocess seam (`_run_lean`) and the
`lean_available` probe: everything *around* Lean — MathNode→Lean translation,
the hybrid auto/proof-carrying decision, caching, and the grade.py wiring — is
exercised here. The Lean invocation itself is verified in CI / the container.

Runnable standalone:  python tests/test_lean_prover.py
"""
from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import grade
import lean_check
import lean_prover
from lean_check import _bin, _frac, _num, _neg, A, B, C


# --- a stub Lean: succeeds on a configurable allow-list of theorem bodies ------
class FakeLean:
    """Stands in for the kernel. `accept(body) -> bool` decides each call."""
    def __init__(self, accept):
        self.accept = accept
        self.calls: list[str] = []

    def __call__(self, body: str):
        self.calls.append(body)
        return (True, "") if self.accept(body) else (False, "unsolved goals")


def _install(monkey_accept):
    lean_prover._CACHE.clear()
    lean_prover.lean_available = lambda: True          # type: ignore[assignment]
    fake = FakeLean(monkey_accept)
    lean_prover._run_lean = fake                       # type: ignore[assignment]
    return fake


def test_translation_arithmetic():
    assert lean_prover.to_lean(A) == "a"
    assert lean_prover.to_lean(_num(1)) == "(1 : ℚ)"
    assert lean_prover.to_lean(_bin("add", A, B)) == "(a + b)"
    assert lean_prover.to_lean(_frac(A, B)) == "(a / b)"
    assert lean_prover.to_lean(_neg(A)) == "(-a)"
    assert lean_prover.wild_names(_bin("mul", _bin("add", A, B), C)) == ["a", "b", "c"]


def test_goal_and_hyps():
    rule = {"id": "frac_cancel", "lhs": _frac(_bin("mul", C, A), _bin("mul", C, B)),
            "rhs": _frac(A, B), "conditions": [{"kind": "nonzero", "var": "c"}]}
    sig, nz = lean_prover._goal(rule)
    assert "∀ (a b c : ℚ)" in sig
    assert "(h0 : c ≠ 0)" in sig
    assert sig.strip().endswith("((c * a) / (c * b)) = (a / b)")
    assert nz == ["h0"]


def test_auto_prove_sound_rule():
    fake = _install(lambda body: True)               # Lean proves anything
    r = lean_prover.prove_rule({"id": "my_add_comm", "lhs": _bin("add", A, B),
                                "rhs": _bin("add", B, A), "conditions": []})
    assert r.proven and r.method == "ring"
    assert "ring" in fake.calls[0]


def test_auto_prove_rejects_unsound_rule():
    # The classic missing-guard rule: x/x = 1 unconditionally. Lean refuses it.
    _install(lambda body: False)
    r = lean_prover.prove_rule({"id": "frac_self_one_BROKEN", "lhs": _frac(A, A),
                                "rhs": _num(1), "conditions": []})
    assert not r.proven and r.method == "rejected"


def test_proof_carrying_fallback():
    # auto-prove fails (relational rule), but a supplied proof checks out.
    fake = _install(lambda body: "import Mathlib\n" in body)  # only the carried file imports full Mathlib
    r = lean_prover.prove_rule({"id": "eq_symm", "lhs": _bin("eq", A, B),
                                "rhs": _bin("eq", B, A), "bidirectional": True,
                                "proof": "exact eq_comm"})
    assert r.proven and r.method == "proof"


def test_cache_dedupes_by_content():
    fake = _install(lambda body: True)
    rule = {"id": "r1", "lhs": _bin("add", A, B), "rhs": _bin("add", B, A), "conditions": []}
    lean_prover.prove_rule(rule)
    lean_prover.prove_rule({**rule, "id": "r2"})      # same body, different id
    assert len(fake.calls) == 1                        # proven once, reused


def test_grade_certifies_derivation_under_custom_rule():
    _install(lambda body: True)
    src = _bin("add", {"type": "variable", "value": "x"}, {"type": "variable", "value": "y"})
    tgt = _bin("add", {"type": "variable", "value": "y"}, {"type": "variable", "value": "x"})
    req = {"protocol": "1.0",
           "exercise": {"mode": "transformation", "source": src, "target": tgt,
                        "ruleset": [{"id": "my_add_comm", "owner": "add", "lhs": _bin("add", A, B),
                                     "rhs": _bin("add", B, A), "bidirectional": True,
                                     "conditions": []}]},
           "submission": {"steps": [{"kind": "A", "rule": "my_add_comm", "path": [],
                                     "direction": "forward"}]}}
    resp = grade.grade(req)
    assert resp["outcome"] == "proven_equal" and resp["certified"] and resp["score"] == 100
    assert resp["meta"]["ruleset"]["my_add_comm"]["method"] == "ring"


def test_grade_unknown_when_rule_unproven():
    _install(lambda body: False)                       # Lean rejects the (unsound) rule
    src = _frac({"type": "variable", "value": "x"}, {"type": "variable", "value": "x"})
    req = {"protocol": "1.0",
           "exercise": {"mode": "transformation", "source": src, "target": _num(1),
                        "ruleset": [{"id": "bad", "owner": "frac", "lhs": _frac(A, A),
                                     "rhs": _num(1), "bidirectional": False, "conditions": []}]},
           "submission": {"steps": [{"kind": "A", "rule": "bad", "path": [],
                                     "direction": "forward"}]}}
    resp = grade.grade(req)
    assert resp["outcome"] == "unknown" and resp["score"] is None
    assert resp["meta"]["ruleset"]["bad"]["proven"] is False


def test_grade_unknown_when_lean_unavailable():
    lean_prover._CACHE.clear()
    lean_prover.lean_available = lambda: False          # type: ignore[assignment]
    req = {"protocol": "1.0",
           "exercise": {"mode": "transformation", "source": _num(1), "target": _num(1),
                        "ruleset": [{"id": "x", "lhs": _bin("add", A, B), "rhs": _bin("add", B, A),
                                     "conditions": []}]},
           "submission": {"final": _num(1)}}
    resp = grade.grade(req)
    assert resp["outcome"] == "unknown"


def _run_all():
    fns = [v for k, v in sorted(globals().items()) if k.startswith("test_") and callable(v)]
    for fn in fns:
        # restore real probes between tests; each test installs what it needs
        lean_prover.lean_available = lean_prover.lean_available
        fn()
        print(f"  ok  {fn.__name__}")
    print(f"\n{len(fns)} passed")


if __name__ == "__main__":
    _run_all()
