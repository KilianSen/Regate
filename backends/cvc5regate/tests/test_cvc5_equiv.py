from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import cvc5_equiv
import cvc5_induction
import cvc5_prover
import grade


# ---- MathNode builders ----
def num(v): return {"type": "number", "value": str(v)}
def vr(v): return {"type": "variable", "value": v}
def wd(v): return {"type": "wild", "value": v}
def bb(t, l, r): return {"type": t, "slots": {"left": [l], "right": [r]}}
def add(l, r): return bb("add", l, r)
def mul(l, r): return bb("mul", l, r)
def eq(l, r): return bb("eq", l, r)
def rule(rid, lhs, rhs, **kw): return {"id": rid, "lhs": lhs, "rhs": rhs, **kw}


ADD_ZERO = rule("add_zero_right", add(wd("a"), num(0)), wd("a"))


# ---- a stub cvc5 driven by the solver flags ---------------------------------
class FakeCvc5:
    """`respond(kind, source) -> (verdict, detail)` where kind is 'disprove'
    (--fmf-fun), 'prove-ind' (--quant-ind), or 'prove' (plain)."""
    def __init__(self, respond):
        self.respond = respond
        self.calls: list[tuple[str, list]] = []

    def __call__(self, source, extra_args=None, timeout=None):
        args = extra_args or []
        self.calls.append((source, args))
        kind = ("disprove" if "--fmf-fun" in args
                else "prove-ind" if "--quant-ind" in args else "prove")
        return self.respond(kind, source)


def _install(respond, cvc5=True, carcara=False):
    cvc5_prover._CACHE.clear()
    cvc5_induction._CACHE.clear()
    cvc5_induction._RULE_CACHE.clear()
    cvc5_equiv._CACHE.clear()
    cvc5_prover.cvc5_available = lambda: cvc5           # type: ignore[assignment]
    cvc5_prover.carcara_available = lambda: carcara     # type: ignore[assignment]
    cvc5_prover._run_cvc5 = FakeCvc5(respond)           # type: ignore[assignment]


def _tx(source, target, submission, **exkw):
    ex = {"mode": "transformation", "source": source, "target": target, **exkw}
    return grade.grade({"protocol": "1.0", "exercise": ex, "submission": submission})


# --------------------------------------------------------------------------- #
# Endpoint equivalence via the SMT oracle.
# --------------------------------------------------------------------------- #
def test_reached_target_form_needs_no_solver():
    # final is structurally the target — decided without invoking cvc5.
    _install(lambda k, s: (_ for _ in ()).throw(AssertionError("cvc5 must not be called")))
    r = _tx(add(vr("x"), num(0)), vr("x"), {"final": vr("x")})
    # target here is `x`; final is `x` → 100, empty certificate.
    assert r["outcome"] == "proven_equal" and r["score"] == 100 and r["proof"] == []


def test_disprove_yields_proven_unequal_with_witness():
    _install(lambda k, s: ("sat", "sat\n((x 0))") if k == "disprove" else ("unknown", ""))
    r = _tx(add(vr("x"), num(1)), vr("x"), {"final": add(vr("x"), num(1))})
    assert r["outcome"] == "proven_unequal" and r["score"] == 0
    assert r["certified"] is True and r["witness"] == {"x": "0"}


def test_prove_yields_proven_equal_partial_credit():
    # No counterexample, cvc5 proves equivalence. Final is equivalent but not the
    # target *form*, and strictly closer than the source → a partial 1..99 score.
    _install(lambda k, s: ("unknown", "") if k == "disprove" else ("unsat", "unsat"))
    src = add(add(vr("x"), num(0)), num(0))
    r = _tx(src, vr("x"), {"final": add(vr("x"), num(0))})
    assert r["outcome"] == "proven_equal" and 1 <= r["score"] <= 99
    assert r["certified"] is True and r["proof"][0]["engine"] == "cvc5"


def test_partial_credit_off_is_binary():
    _install(lambda k, s: ("unknown", "") if k == "disprove" else ("unsat", "unsat"))
    src = add(add(vr("x"), num(0)), num(0))
    r = _tx(src, vr("x"), {"final": add(vr("x"), num(0))},
            options={"partial_credit": False})
    assert r["outcome"] == "proven_equal" and r["score"] == 0


def test_unknown_when_solver_inconclusive():
    _install(lambda k, s: ("unknown", "") )
    r = _tx(add(vr("x"), num(1)), vr("y"), {"final": add(vr("x"), num(1))})
    assert r["outcome"] == "unknown" and r["score"] is None


def test_require_recheck_no_carcara():
    cvc5_induction.REQUIRE_RECHECK = True
    try:
        _install(lambda k, s: ("unknown", "") if k == "disprove" else ("unsat", "unsat"),
                 carcara=False)
        r = _tx(mul(num(2), add(vr("x"), vr("y"))),
                add(mul(num(2), vr("x")), mul(num(2), vr("y"))),
                {"final": mul(num(2), add(vr("x"), vr("y")))})
        assert r["outcome"] == "equal_no_certificate" and r["score"] is None
        assert r["certified"] is False
    finally:
        cvc5_induction.REQUIRE_RECHECK = False


def test_cvc5_unavailable_still_decides_target_form():
    _install(lambda k, s: ("error", ""), cvc5=False)
    # structural match still works with no solver...
    r = _tx(vr("x"), vr("x"), {"final": vr("x")})
    assert r["outcome"] == "proven_equal" and r["score"] == 100
    # ...but a genuine equivalence question is unknown without the solver.
    r2 = _tx(add(vr("x"), num(0)), vr("x"), {"final": add(vr("x"), num(0))})
    assert r2["outcome"] == "unknown"


# --------------------------------------------------------------------------- #
# Submitted derivations (symbolic, rules trusted by default).
# --------------------------------------------------------------------------- #
def test_derivation_certified_no_solver():
    _install(lambda k, s: (_ for _ in ()).throw(AssertionError("cvc5 must not be called")))
    r = _tx(add(vr("x"), num(0)), vr("x"),
            {"steps": [{"kind": "A", "rule": "add_zero_right", "path": [], "result": vr("x")}]},
            ruleset=[ADD_ZERO])
    assert r["outcome"] == "proven_equal" and r["score"] == 100 and r["certified"] is True
    assert r["steps"][0]["status"] == "valid"
    assert r["proof"][0]["rule"] == "add_zero_right"


def test_derivation_invalid_wrong_result():
    _install(lambda k, s: (_ for _ in ()).throw(AssertionError("cvc5 must not be called")))
    r = _tx(add(vr("x"), num(0)), vr("x"),
            {"steps": [{"kind": "A", "rule": "add_zero_right", "path": [], "result": num(5)}]},
            ruleset=[ADD_ZERO])
    assert r["outcome"] == "invalid_derivation" and r["score"] == 0
    assert r["steps"][0]["status"] == "invalid"


def test_unknown_rule_falls_back_to_oracle():
    # The step cites a rule not in the ruleset → the derivation is uncertifiable, so
    # we grade the claimed endpoint with the oracle (here: refuted with a witness).
    _install(lambda k, s: ("sat", "sat\n((x 0))") if k == "disprove" else ("unknown", ""))
    r = _tx(add(vr("x"), num(0)), vr("x"),
            {"steps": [{"kind": "A", "rule": "no_such_rule", "path": [], "result": add(vr("x"), num(1))}]},
            ruleset=[ADD_ZERO])
    assert r["outcome"] == "proven_unequal" and r["witness"] == {"x": "0"}
    assert r["steps"][0]["status"] == "open"


def test_equation_mode_holds():
    _install(lambda k, s: ("unknown", "") if k == "disprove" else ("unsat", "unsat"))
    r = grade.grade({"protocol": "1.0",
                     "exercise": {"mode": "equation", "source": eq(add(vr("x"), num(0)), vr("x"))},
                     "submission": {"final": eq(add(vr("x"), num(0)), vr("x"))}})
    assert r["outcome"] == "proven_equal" and r["score"] == 100


def test_equation_mode_false():
    _install(lambda k, s: ("sat", "sat\n((x 0))") if k == "disprove" else ("unknown", ""))
    r = grade.grade({"protocol": "1.0",
                     "exercise": {"mode": "equation", "source": eq(add(vr("x"), num(1)), vr("x"))},
                     "submission": {"final": eq(add(vr("x"), num(1)), vr("x"))}})
    assert r["outcome"] == "proven_unequal" and r["witness"] == {"x": "0"}


def test_unsupported_mode_rejected():
    try:
        grade.grade({"protocol": "1.0", "exercise": {"mode": "nonsense", "source": vr("x")}})
        assert False, "expected RequestError"
    except grade.RequestError:
        pass


def _run_all():
    fns = [g for n, g in sorted(globals().items()) if n.startswith("test_") and callable(g)]
    for fn in fns:
        fn()
        print(f"  ok  {fn.__name__}")
    print(f"\n{len(fns)} passed")


if __name__ == "__main__":
    _run_all()
