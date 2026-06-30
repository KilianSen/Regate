"""Tests for cvc5regate. cvc5 may or may not be present; the bulk of these stub
the single subprocess seam (`cvc5_prover._run_cvc5`) and the `cvc5_available`
probe so everything *around* cvc5 — MathNode→SMT translation, type inference, the
certify/disprove-first decision, caching, and the grade.py wiring — runs without a
solver. A final block of tests is gated on a real cvc5 being available and
exercises it end-to-end.

Runnable standalone:  python tests/test_cvc5_prover.py
"""
from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import cvc5_induction
import cvc5_prover
import grade


# ---- MathNode builders ----
def num(v): return {"type": "number", "value": str(v)}
def vr(v): return {"type": "variable", "value": v}
def wd(v): return {"type": "wild", "value": v}
def bb(t, l, r): return {"type": t, "slots": {"left": [l], "right": [r]}}
def mul(l, r): return bb("mul", l, r)
def add(l, r): return bb("add", l, r)
def sub(l, r): return bb("sub", l, r)
def eq(l, r): return bb("eq", l, r)
def ge(l, r): return bb("ge", l, r)
def succ(x): return {"type": "succ", "slots": {"inner": [x]}}
def powr(b, e): return {"type": "pow", "slots": {"base": [b], "exponent": [e]}}
def app(name, *a): return {"type": "apply", "value": name, "slots": {"args": list(a)}}
def divides(d, v): return {"type": "divides", "slots": {"divisor": [num(d)], "value": [v]}}
def rule(rid, lhs, rhs): return {"id": rid, "lhs": lhs, "rhs": rhs}

POW = [rule("pow_zero", powr(wd("a"), num(0)), num(1)),
       rule("pow_succ", powr(wd("a"), succ(wd("k"))), mul(wd("a"), powr(wd("a"), wd("k"))))]
SUM = [rule("sum_zero", app("sum", num(0)), num(0)),
       rule("sum_succ", app("sum", succ(wd("k"))), add(succ(wd("k")), app("sum", wd("k"))))]

POW_GOAL = {"mode": "induction", "goal": eq(powr(num(1), vr("n")), num(1)),
            "inductionVar": "n", "definitions": POW}
DIV_GOAL = {"mode": "induction", "domain": "int",
            "goal": divides(3, sub(mul(vr("n"), mul(vr("n"), vr("n"))), vr("n"))),
            "inductionVar": "n", "definitions": []}


# ---- a stub cvc5: verdicts driven by a callable -----------------------------
class FakeCvc5:
    """Stands in for the solver. `respond(source, args) -> (verdict, detail)`."""
    def __init__(self, respond):
        self.respond = respond
        self.calls: list[tuple[str, list]] = []

    def __call__(self, source, extra_args=None, timeout=None):
        self.calls.append((source, extra_args or []))
        return self.respond(source, extra_args or [])


def _install(respond):
    cvc5_prover._CACHE.clear()
    cvc5_induction._CACHE.clear()
    cvc5_prover.cvc5_available = lambda: True            # type: ignore[assignment]
    cvc5_prover.carcara_available = lambda: False        # type: ignore[assignment]
    fake = FakeCvc5(respond)
    cvc5_prover._run_cvc5 = fake                          # type: ignore[assignment]
    return fake


# --- translation (no cvc5) ---------------------------------------------------
def test_translate_pow_goal():
    src = cvc5_induction.build_prove_source(POW_GOAL)
    assert "(declare-datatype Nat ((zero) (succ (pred Nat))))" in src
    assert "define-fun-rec pow" in src
    assert "(assert (not (forall ((n Nat))" in src   # negated universal over Nat
    assert src.rstrip().endswith("(check-sat)")


def test_translate_divisibility_uses_int_and_mod():
    src = cvc5_induction.build_prove_source(DIV_GOAL)
    assert "(mod" in src and ") 3) 0)" in src
    assert "define-fun-rec val ((n Nat)) Int" in src    # the ℕ→Int coercion


def test_translate_recursive_sum():
    ex = {"mode": "induction", "domain": "int",
          "goal": eq(mul(num(2), app("sum", vr("n"))), mul(vr("n"), add(vr("n"), num(1)))),
          "inductionVar": "n", "definitions": SUM}
    src = cvc5_induction.build_prove_source(ex)
    assert "define-fun-rec sum" in src
    assert "(sum n)" in src


def test_disprove_source_has_free_const_and_getvalue():
    src, labels = cvc5_induction.build_disprove_source(POW_GOAL)
    assert "(declare-const n Nat)" in src
    assert "(check-sat)" in src and "(get-value ((val n)))" in src
    assert labels == ["n"]


def test_induction_var_forced_nat_even_in_numeric_position():
    # In `3 | n^3-n` the variable n appears only as a number, yet must be ℕ.
    _, _, var, num_vars = cvc5_induction._translate(DIV_GOAL)
    assert var == "n" and num_vars == []   # n is the ℕ var, no numeric vars


def test_number_and_nat_literals():
    assert cvc5_induction._num_lit("1", "Real") == "1.0"
    assert cvc5_induction._num_lit("3", "Int") == "3"
    assert cvc5_induction._num_lit("-2", "Int") == "(- 2)"
    assert cvc5_induction._nat_lit(0) == "zero"
    assert cvc5_induction._nat_lit(2) == "(succ (succ zero))"


def test_untranslatable_goal_is_unknown():
    fake = _install(lambda s, a: ("unsat", ""))
    ex = {"mode": "induction", "goal": {"type": "weird"}, "inductionVar": "n"}
    res = cvc5_induction.certify(ex)
    assert res.outcome == "unknown" and res.method == "untranslatable"
    assert not fake.calls   # never even reached the solver


# --- certify decision logic (stubbed cvc5) -----------------------------------
def test_unsat_certifies_proven_equal():
    # disprove pass: no counterexample (unknown); prove pass: unsat.
    _install(lambda s, a: ("unknown", "") if "--fmf-fun" in a else ("unsat", ""))
    res = cvc5_induction.certify(POW_GOAL)
    assert res.outcome == "proven_equal" and res.certified and res.method == "quant-ind"


def test_sat_with_model_is_proven_unequal_with_witness():
    def respond(s, a):
        if "--fmf-fun" in a:
            return "sat", "sat\n(((val n) 2))"
        return "unsat", ""
    _install(respond)
    res = cvc5_induction.certify(POW_GOAL)
    assert res.outcome == "proven_unequal" and res.witness == {"n": "2"}
    assert not res.certified


def test_unknown_stays_unknown():
    _install(lambda s, a: ("unknown", "timeout"))
    res = cvc5_induction.certify(POW_GOAL)
    assert res.outcome == "unknown"


def test_unavailable_is_unknown():
    cvc5_prover._CACHE.clear(); cvc5_induction._CACHE.clear()
    cvc5_prover.cvc5_available = lambda: False            # type: ignore[assignment]
    res = cvc5_induction.certify(POW_GOAL)
    assert res.outcome == "unknown" and res.method == "unavailable"


def test_require_recheck_downgrades_unrechecked_unsat():
    _install(lambda s, a: ("unknown", "") if "--fmf-fun" in a else ("unsat", ""))
    cvc5_induction.REQUIRE_RECHECK = True
    try:
        res = cvc5_induction.certify(POW_GOAL)
        assert res.outcome == "equal_no_certificate" and not res.certified
    finally:
        cvc5_induction.REQUIRE_RECHECK = False


# --- grade.py wiring ---------------------------------------------------------
def test_grade_induction_certified():
    _install(lambda s, a: ("unknown", "") if "--fmf-fun" in a else ("unsat", ""))
    resp = grade.grade({"protocol": "1.0", "exercise": POW_GOAL})
    assert resp["outcome"] == "proven_equal" and resp["certified"] and resp["score"] == 100
    assert resp["proof"] and resp["proof"][0]["engine"] == "cvc5"


def test_grade_induction_disproved_carries_witness():
    def respond(s, a):
        return ("sat", "sat\n(((val n) 2))") if "--fmf-fun" in a else ("unsat", "")
    _install(respond)
    resp = grade.grade({"protocol": "1.0", "exercise": POW_GOAL})
    assert resp["outcome"] == "proven_unequal" and resp["score"] == 0
    assert resp["witness"] == {"n": "2"}


def test_grade_non_induction_is_unknown():
    resp = grade.grade({"protocol": "1.0",
                        "exercise": {"mode": "transformation", "source": num(1), "target": num(1)},
                        "submission": {"final": num(1)}})
    assert resp["outcome"] == "unknown" and resp["score"] is None


def test_grade_malformed_raises():
    for ex in ({"mode": "induction"},                       # no goal
               {"mode": "induction", "goal": POW_GOAL["goal"]}):  # no inductionVar
        try:
            grade.grade({"protocol": "1.0", "exercise": ex})
            assert False, "expected RequestError"
        except grade.RequestError:
            pass


def test_grade_bad_protocol_raises():
    try:
        grade.grade({"protocol": "2.0", "exercise": POW_GOAL})
        assert False
    except grade.RequestError:
        pass


# --- real-solver tests (gated on a cvc5 binary) ------------------------------
def _real_cvc5() -> bool:
    # re-probe through the (possibly stubbed) module by importing a fresh value
    import importlib
    importlib.reload(cvc5_prover)
    return cvc5_prover.cvc5_available()


def test_real_cvc5_end_to_end():
    if not _real_cvc5():
        print("    (skipped real-cvc5 tests: no binary)")
        return
    import importlib
    importlib.reload(cvc5_induction)
    # 1^n = 1 certifies.
    r = cvc5_induction.certify(POW_GOAL)
    assert r.outcome == "proven_equal" and r.certified, r
    # 3 | n^3 - n certifies (outside leanregate's fragment).
    r = cvc5_induction.certify(DIV_GOAL)
    assert r.outcome == "proven_equal", r
    # A false goal is disproved with a numeric witness.
    false_goal = {"mode": "induction", "domain": "int",
                  "goal": eq(powr(num(2), vr("n")), add(vr("n"), num(1))),
                  "inductionVar": "n", "definitions": POW}
    r = cvc5_induction.certify(false_goal)
    assert r.outcome == "proven_unequal" and r.witness, r


def _run_all():
    fns = [v for k, v in sorted(globals().items()) if k.startswith("test_") and callable(v)]
    for fn in fns:
        fn()
        print(f"  ok  {fn.__name__}")
    print(f"\n{len(fns)} passed")


if __name__ == "__main__":
    _run_all()
