"""`exercise.assumptions` on cvc5regate's SMT paths.

The bug these pin: cvc5regate never read `exercise.assumptions`, and SMT-LIB leaves
`(/ x 0)` underspecified — so the counterexample search returned `x = 0` as a
"counterexample" to `x/x = 1` even when the exercise declared `x ≠ 0`. That is a
WRONG GRADE (`proven_unequal`, score 0, on a correct answer) and a conformance
divergence: eggregate answers `proven_equal` on the identical request.

Three invariants are pinned here:
  1. the assumptions reach BOTH queries — asserted in the disprove source, a
     hypothesis in the prove source;
  2. an assumption kind with no sound SMT translation makes the query DECLINE
     (`unknown`) — never silently dropped, which is what caused the bug;
  3. fail-safe: a counterexample that cannot be *shown* to satisfy the assumptions
     degrades to `unknown`, never `proven_unequal` (mirrors D4 `_usable_witness`).
And the behaviour that must NOT regress: with no assumptions declared, `x/x = 1`
really is refuted at `x = 0`.
"""
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
def frac(n, d): return {"type": "frac", "slots": {"numerator": [n], "denominator": [d]}}
def powr(b, e): return {"type": "pow", "slots": {"base": [b], "exponent": [e]}}
def succ(x): return {"type": "succ", "slots": {"inner": [x]}}


NONZERO_X = [{"kind": "nonzero", "value": vr("x")}]
X_OVER_X = frac(vr("x"), vr("x"))
POW = [{"id": "pow_zero", "lhs": powr(wd("a"), num(0)), "rhs": num(1)},
       {"id": "pow_succ", "lhs": powr(wd("a"), succ(wd("k"))),
        "rhs": mul(wd("a"), powr(wd("a"), wd("k")))}]


# ---- a stub cvc5 driven by the solver flags (mirrors test_cvc5_equiv) -------
class FakeCvc5:
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
    fake = FakeCvc5(respond)
    cvc5_prover._run_cvc5 = fake                        # type: ignore[assignment]
    return fake


def _honest(kind, source):
    """A solver that behaves like the real one on `x/x = 1`: `x = 0` is a model only
    when nothing rules it out, and the guarded equivalence is valid."""
    guarded = "(not (= x 0.0))" in source
    if kind == "disprove":
        return ("unsat", "unsat") if guarded else ("sat", "sat\n((x 0.0))")
    return ("unsat", "unsat") if guarded else ("unknown", "")


def _always_sat_at_zero(kind, source):
    """A solver that hands back `x = 0` whatever we asserted — stands in for any
    future translation gap. The fail-safe must still refuse to grade on it."""
    return ("sat", "sat\n((x 0.0))") if kind == "disprove" else ("unknown", "")


def _tx(submission, assumptions=None, source=None, target=None, **exkw):
    ex = {"mode": "transformation",
          "source": X_OVER_X if source is None else source,
          "target": num(1) if target is None else target, **exkw}
    if assumptions is not None:
        ex["assumptions"] = assumptions
    return grade.grade({"protocol": "1.1", "exercise": ex, "submission": submission})


# --------------------------------------------------------------------------- #
# 1) The assumptions reach both SMT queries.
# --------------------------------------------------------------------------- #
def test_assumption_is_asserted_in_the_equiv_disprove_query():
    ex = {"mode": "transformation", "source": X_OVER_X, "target": num(1),
          "assumptions": NONZERO_X}
    src, labels = cvc5_equiv.build_disprove_source(ex, X_OVER_X, num(1))
    assert "(assert (not (= x 0.0)))" in src        # the excluded point is ruled out
    assert "(assert (not (= (/ x x) 1.0)))" in src
    assert labels == ["x"]


def test_assumption_is_a_hypothesis_in_the_equiv_prove_query():
    ex = {"mode": "transformation", "source": X_OVER_X, "target": num(1),
          "assumptions": NONZERO_X}
    src = cvc5_equiv.build_prove_source(ex, X_OVER_X, num(1))
    # `x/x = 1` is a theorem only *under* `x != 0` — it must be the antecedent.
    assert "(=> (not (= x 0.0)) (= (/ x x) 1.0))" in src
    assert "(forall ((x Real))" in src


def test_positive_and_integer_translate_multiple_assumptions_conjunctively():
    ex = {"mode": "transformation", "source": vr("x"), "target": vr("x"),
          "assumptions": [{"kind": "positive", "value": vr("x")},
                          {"kind": "integer", "value": add(vr("x"), num(1))}]}
    src = cvc5_equiv.build_prove_source(ex, vr("x"), vr("x"))
    assert "(and (> x 0.0) (is_int (+ x 1.0)))" in src


def test_integer_assumption_is_trivial_in_the_integer_domain():
    ex = {"mode": "transformation", "domain": "int", "source": vr("x"), "target": vr("x"),
          "assumptions": [{"kind": "integer", "value": vr("x")}]}
    src = cvc5_equiv.build_prove_source(ex, vr("x"), vr("x"))
    assert "is_int" not in src and "(=> true" in src   # integral by construction in ℤ


def test_assumption_only_variable_is_still_declared():
    # A variable mentioned by an assumption alone must be declared/bound, or the
    # emitted file references an unknown symbol and the query dies as `error`.
    ex = {"mode": "transformation", "source": vr("x"), "target": vr("x"),
          "assumptions": [{"kind": "nonzero", "value": vr("y")}]}
    dis, labels = cvc5_equiv.build_disprove_source(ex, vr("x"), vr("x"))
    assert "(declare-const y Real)" in dis and "y" in labels
    assert "(y Real)" in cvc5_equiv.build_prove_source(ex, vr("x"), vr("x"))


# --------------------------------------------------------------------------- #
# 2) The reproduced wrong grade, end to end.
# --------------------------------------------------------------------------- #
def test_guarded_division_is_not_proven_unequal():
    # THE BUG: `x/x` vs `1` under `x != 0`, submission = the source so the oracle runs.
    _install(_honest)
    r = _tx({"final": X_OVER_X}, assumptions=NONZERO_X)
    assert r["outcome"] != "proven_unequal"
    # ...and with the assumption as a hypothesis cvc5 proves it — same verdict as
    # eggregate on the identical request (`proven_equal`, no progress toward the form).
    assert r["outcome"] == "proven_equal" and r["score"] == 0
    assert r["witness"] is None


def test_assumption_free_division_is_still_proven_unequal():
    # NOT a regression to fix: with nothing declared, `x/x = 1` is genuinely false at
    # x = 0 and the witness is the right answer.
    _install(_honest)
    r = _tx({"final": X_OVER_X})
    assert r["outcome"] == "proven_unequal" and r["score"] == 0
    assert r["witness"] == {"x": "0.0"}


def test_deleting_the_assumption_changes_the_query():
    # The field must be load-bearing: same request ± `assumptions` ⇒ different SMT.
    ex = {"mode": "transformation", "source": X_OVER_X, "target": num(1)}
    bare = cvc5_equiv.build_prove_source(ex, X_OVER_X, num(1))
    guarded = cvc5_equiv.build_prove_source({**ex, "assumptions": NONZERO_X},
                                            X_OVER_X, num(1))
    assert bare != guarded


# --------------------------------------------------------------------------- #
# 3) Fail-safe: a witness we cannot vouch for is never a grade.
# --------------------------------------------------------------------------- #
def test_witness_violating_an_assumption_degrades_to_unknown():
    _install(_always_sat_at_zero)
    r = _tx({"final": X_OVER_X}, assumptions=NONZERO_X)
    assert r["outcome"] == "unknown" and r["score"] is None
    assert r["witness"] is None


def test_witness_check_rejects_unevaluable_assumption_terms():
    # `cannot be shown to satisfy` — an assumption over a term outside the rational
    # fragment (a recursive `apply`) is not re-checkable, so the witness fails safe.
    ex = {"assumptions": [{"kind": "nonzero",
                           "value": {"type": "apply", "value": "f",
                                     "slots": {"args": [vr("x")]}}}]}
    assert cvc5_induction.witness_respects_assumptions(ex, {"x": "0.0"}) is False
    # ...and an unbound variable likewise.
    ex2 = {"assumptions": [{"kind": "nonzero", "value": vr("y")}]}
    assert cvc5_induction.witness_respects_assumptions(ex2, {"x": "1"}) is False


def test_witness_check_accepts_an_admitted_point():
    ex = {"assumptions": [{"kind": "nonzero", "value": vr("x")},
                          {"kind": "positive", "value": add(vr("x"), num(1))},
                          {"kind": "integer", "value": vr("x")}]}
    assert cvc5_induction.witness_respects_assumptions(ex, {"x": "2"}) is True
    assert cvc5_induction.witness_respects_assumptions(ex, {"x": "0.0"}) is False   # nonzero
    assert cvc5_induction.witness_respects_assumptions(ex, {"x": "-3"}) is False    # positive
    assert cvc5_induction.witness_respects_assumptions(ex, {"x": "1.5"}) is False   # integer
    assert cvc5_induction.witness_respects_assumptions({}, {"x": "0.0"}) is True    # none declared


# --------------------------------------------------------------------------- #
# 4) Untranslatable kinds decline; malformed ones are a 400.
# --------------------------------------------------------------------------- #
def test_untranslatable_assumption_kind_declines():
    # `constant` is a syntactic property of a matched subterm, not a constraint on a
    # numeric model — there is no sound SMT reading, so the query declines rather
    # than dropping it. cvc5 is never even consulted.
    _install(lambda k, s: (_ for _ in ()).throw(AssertionError("cvc5 must not be called")))
    r = _tx({"final": X_OVER_X}, assumptions=[{"kind": "constant", "value": vr("x")}])
    assert r["outcome"] == "unknown" and r["score"] is None
    assert "constant" in r["feedback"]


def test_unknown_assumption_kind_declines():
    _install(lambda k, s: (_ for _ in ()).throw(AssertionError("cvc5 must not be called")))
    r = _tx({"final": X_OVER_X}, assumptions=[{"kind": "unicorn", "value": vr("x")}])
    assert r["outcome"] == "unknown" and r["score"] is None


def test_malformed_assumption_is_a_request_error():
    for bad in ({"kind": "nonzero"},                       # no value
                {"value": vr("x")},                        # no kind
                {"kind": "nonzero", "value": {"type": "frac"}},   # malformed MathNode
                "nonzero"):                                # not an object
        try:
            _tx({"final": X_OVER_X}, assumptions=[bad])
            assert False, f"expected RequestError for {bad!r}"
        except grade.RequestError:
            pass
    try:
        _tx({"final": X_OVER_X}, assumptions={"kind": "nonzero", "value": vr("x")})
        assert False, "expected RequestError for a non-list assumptions"
    except grade.RequestError:
        pass


# --------------------------------------------------------------------------- #
# 5) The induction path had the same hole.
# --------------------------------------------------------------------------- #
_IND_EX = {"mode": "induction", "inductionVar": "n", "definitions": POW,
           "goal": eq(powr(X_OVER_X, vr("n")), num(1)),
           "assumptions": NONZERO_X}


def test_induction_assumption_reaches_both_queries():
    prove = cvc5_induction.build_prove_source(_IND_EX)
    assert "(=> (not (= x 0.0)) (= (pow (/ x x) n) 1.0))" in prove
    dis, labels = cvc5_induction.build_disprove_source(_IND_EX)
    # `(not (=> guard goal))` is `guard AND NOT goal` — the search stays inside the
    # exercise's domain.
    assert "(assert (not (=> (not (= x 0.0)) (= (pow (/ x x) n) 1.0))))" in dis
    assert set(labels) == {"x", "n"}


def test_induction_witness_violating_an_assumption_degrades_to_unknown():
    _install(_always_sat_at_zero)
    res = cvc5_induction.certify(_IND_EX)
    assert res.outcome == "unknown" and res.witness is None
    # Without the assumption the same model IS a counterexample and must be reported.
    _install(_always_sat_at_zero)
    bare = {k: v for k, v in _IND_EX.items() if k != "assumptions"}
    res2 = cvc5_induction.certify(bare)
    assert res2.outcome == "proven_unequal" and res2.witness == {"x": "0.0"}


def test_induction_untranslatable_assumption_declines():
    _install(lambda k, s: (_ for _ in ()).throw(AssertionError("cvc5 must not be called")))
    res = cvc5_induction.certify({**_IND_EX,
                                  "assumptions": [{"kind": "constant", "value": vr("x")}]})
    assert res.outcome == "unknown" and res.method == "untranslatable"


def test_induction_grading_does_not_refute_an_assumed_goal():
    _install(_always_sat_at_zero)
    res = cvc5_induction.grade_derivation(_IND_EX, {"base": {"steps": []}, "step": {"steps": []}})
    assert res.status != "refuted" and res.witness is None


# --------------------------------------------------------------------------- #
# 6) The trust boundary is untouched: rule *verification* ignores the exercise's
#    assumptions — a rule is proven as transmitted, not under the student's domain.
# --------------------------------------------------------------------------- #
def test_rule_verification_ignores_exercise_assumptions():
    ex = {"mode": "transformation", "source": vr("x"), "target": vr("x"),
          "assumptions": NONZERO_X, "options": {"verify_rules": True}}
    rule = {"id": "frac_self_one", "lhs": frac(wd("x"), wd("x")), "rhs": num(1)}
    src = cvc5_induction.build_rule_source(rule, ex)
    assert "(not (= x 0.0))" not in src          # the wildcard `x` is NOT the exercise's x
    opted_in = cvc5_induction.build_rule_source(rule, ex, use_assumptions=True)
    assert "(not (= x 0.0))" in opted_in


def test_unguarded_false_rule_is_still_rejected_under_assumptions():
    # The regression the flag above prevents: `x/x = 1` is transmitted unguarded, the
    # exercise assumes `x != 0`, and verify_rules must still not certify the rule.
    # The stub only settles a query that carries the guard; the rule query must not.
    _install(lambda k, s: ("unsat", "unsat") if "(not (= x 0.0))" in s else ("sat", "sat"))
    ex = {"mode": "transformation", "source": vr("x"), "target": num(1),
          "assumptions": NONZERO_X, "options": {"verify_rules": True},
          "ruleset": [{"id": "frac_self_one", "lhs": frac(wd("x"), wd("x")), "rhs": num(1)}]}
    proven = cvc5_induction.prove_ruleset(ex)
    assert proven["frac_self_one"].proven is False


def _run_all():
    fns = [g for n, g in sorted(globals().items()) if n.startswith("test_") and callable(g)]
    for fn in fns:
        fn()
        print(f"  ok  {fn.__name__}")
    print(f"\n{len(fns)} passed")


if __name__ == "__main__":
    _run_all()
