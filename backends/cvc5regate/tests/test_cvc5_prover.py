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
    cvc5_induction._RULE_CACHE.clear()
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


# --- grade.py wiring: STRICT rule-instance grading (symbolic) + cvc5 backstop --
# A real valid proof of `1ⁿ = 1`: pow_zero closes the base; pow_succ + the IH +
# mul_one_left close the step. Rules are matched against the transmitted ruleset
# (mul_one_left) + definitions (pow_zero/pow_succ). cvc5 only backstops the leap.
RULESET = [{"id": "mul_one_left", "lhs": mul(num(1), wd("a")), "rhs": wd("a"),
            "bidirectional": False, "conditions": []}]
VALID_BASE = [{"rule": "pow_zero", "path": [0], "result": eq(num(1), num(1))}]
VALID_STEP = [
    {"rule": "pow_succ", "path": [0], "result": eq(mul(num(1), powr(num(1), vr("n"))), num(1))},
    {"kind": "B", "path": [0, 1], "equation": [powr(num(1), vr("n")), num(1)],
     "result": eq(mul(num(1), num(1)), num(1))},
    {"rule": "mul_one_left", "path": [0], "result": eq(num(1), num(1))},
]


def _sub(base, step):
    return {"base": {"steps": [dict(s) for s in base]},
            "step": {"steps": [dict(s) for s in step]}}


def _ind_req(submission, ruleset=RULESET):
    e = {**POW_GOAL, "ruleset": ruleset} if ruleset is not None else POW_GOAL
    return {"protocol": "1.0", "exercise": e, "submission": submission}


def test_grade_induction_certified():
    # backstop: disprove (fmf) not-sat, prove (quant-ind) unsat -> certified
    _install(lambda s, a: ("unknown", "") if "--fmf-fun" in a else ("unsat", ""))
    resp = grade.grade(_ind_req(_sub(VALID_BASE, VALID_STEP)))
    assert resp["outcome"] == "proven_equal" and resp["certified"] and resp["score"] == 100
    assert resp["proof"] and resp["proof"][0]["engine"] == "cvc5"


def test_certified_carries_a_recheckable_proof():
    # The protocol: `certified: true` must carry a proof the caller can re-verify.
    # cvc5 cannot export Alethe for an induction, so the certificate is the SMT-LIB.
    _install(lambda s, a: ("unknown", "") if "--fmf-fun" in a else ("unsat", ""))
    resp = grade.grade(_ind_req(_sub(VALID_BASE, VALID_STEP)))
    proof = resp["proof"][0]
    assert proof["engine"] == "cvc5" and proof["expect"] == "unsat"
    assert "(check-sat)" in proof["smtlib"] and "(assert (not (forall" in proof["smtlib"]
    assert resp["meta"]["rechecked"] is False       # honest: no independent re-check


def test_ruleset_is_trusted_by_default():
    # Regate's premise: the ruleset is authored and formally validated upstream, so
    # the grading path takes the caller's warrant. No solver call is spent on rules.
    fake = _install(lambda s, a: ("unknown", "") if "--fmf-fun" in a else ("unsat", ""))
    resp = grade.grade(_ind_req(_sub(VALID_BASE, VALID_STEP)))
    assert resp["outcome"] == "proven_equal" and resp["certified"]
    assert resp["meta"]["ruleset"]["mul_one_left"]["method"] == "trusted"
    # every solver call carried a flag: none was the bare rule-validity query
    assert all(args for _, args in fake.calls)


def test_verify_rules_rejects_an_unsound_rule():
    # With verify_rules on, the warrant is re-established here. cvc5 certifies the
    # GOAL (1ⁿ = 1, true) but refutes the FALSE rule `a·b = b` the step cites — so
    # the derivation is `unknown`, inconclusive, not a wrong answer.
    unsound = [{"id": "drop_left", "lhs": mul(wd("a"), wd("b")), "rhs": wd("b"),
                "bidirectional": False, "conditions": []}]
    step = [dict(s) for s in VALID_STEP]
    step[2] = dict(step[2], rule="drop_left")

    def respond(src, args):
        if "--fmf-fun" in args:
            return ("unknown", "")                  # no counterexample to the goal
        if "--quant-ind" in args:
            return ("unsat", "")                    # the goal itself is true
        return ("sat", "")                          # ...but the rule is refutable
    _install(respond)
    req = _ind_req(_sub(VALID_BASE, step), ruleset=unsound)
    req["exercise"] = {**req["exercise"], "options": {"verify_rules": True}}
    resp = grade.grade(req)
    assert resp["outcome"] == "unknown" and resp["score"] is None and not resp["certified"]
    assert resp["meta"]["ruleset"]["drop_left"]["proven"] is False


def test_false_goal_returns_proven_unequal_with_witness():
    # `certify` could always build a proven_unequal verdict, but grade_derivation only
    # consulted it after both obligations had certified, so no witness ever escaped.
    def respond(src, args):
        if "--fmf-fun" in args:
            return ("sat", "sat\n(((val n) 0))")    # counterexample at n = 0
        return ("unsat", "")
    _install(respond)
    resp = grade.grade(_ind_req(_sub(VALID_BASE, VALID_STEP)))
    assert resp["outcome"] == "proven_unequal" and resp["score"] == 0
    assert resp["witness"] == {"n": "0"}            # protocol: a witness is mandatory here


def test_grade_induction_invalid_wrong_result():
    _install(lambda s, a: ("unsat", ""))            # symbolic rejects before any backstop
    bad = [dict(VALID_BASE[0], result=eq(num(1), num(2)))]   # pow_zero gives 1=1, not 1=2
    resp = grade.grade(_ind_req(_sub(bad, VALID_STEP)))
    assert resp["outcome"] == "invalid_derivation" and resp["score"] == 0 and not resp["certified"]


def test_grade_induction_invalid_wrong_rule():
    _install(lambda s, a: ("unsat", ""))
    bad = [dict(VALID_BASE[0], rule="pow_succ")]     # pow_succ does not match pow(1,0) — strict
    resp = grade.grade(_ind_req(_sub(bad, VALID_STEP)))
    assert resp["outcome"] == "invalid_derivation" and resp["score"] == 0


def test_grade_induction_unknown_when_unattempted():
    _install(lambda s, a: ("unsat", ""))            # no submission -> never an auto-pass
    resp = grade.grade({"protocol": "1.0", "exercise": POW_GOAL})
    assert resp["outcome"] == "unknown" and resp["score"] is None and not resp["certified"]


def test_grade_induction_unknown_when_backstop_fails():
    _install(lambda s, a: ("unknown", "timeout"))   # steps valid, but cvc5 can't certify the goal
    resp = grade.grade(_ind_req(_sub(VALID_BASE, VALID_STEP)))
    assert resp["outcome"] == "unknown" and resp["score"] is None


def test_certify_disproves_with_witness():
    # The disprove path stays on the certify() oracle: a false goal -> a witness.
    def respond(s, a):
        return ("sat", "sat\n(((val n) 2))") if "--fmf-fun" in a else ("unsat", "")
    _install(respond)
    res = cvc5_induction.certify(POW_GOAL)
    assert res.outcome == "proven_unequal" and res.witness == {"n": "2"}


def test_ac_matching_commutative():
    # `mul_one_left` is `1·a → a`; applied to `x·1` it matches only modulo
    # commutativity. AC off ⇒ no match (invalid); AC on ⇒ closes.
    import step_check as sc
    # `proven=True`: this test is about AC matching, not about the solver's verdict
    # on the rule. An unproven rule is uncertifiable before matching is even tried.
    rules = {"mul_one_left": sc.Rule("mul_one_left", mul(num(1), wd("a")), wd("a"),
                                     proven=True)}
    src = eq(mul(vr("x"), num(1)), vr("x"))                       # x·1 = x
    step = {"rule": "mul_one_left", "path": [0], "result": eq(vr("x"), vr("x"))}
    assert sc.check_case(src, [step], rules, ih=None, ac=()).status == "invalid"
    rep = sc.check_case(src, [step], rules, ih=None, ac=("add", "mul"))
    assert rep.status == "certified" and sc.is_reflexive(rep.final, ("add", "mul"))


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
