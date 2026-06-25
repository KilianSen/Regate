"""Tests that pin Eggregate to the thesis's Appendix B numbers.

Run:  .venv/bin/python -m pytest test_eggregate.py   (or just run this file)
"""
from __future__ import annotations

import os
import sys
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))  # find the package un-installed

from eggregate import (
    Assumption, Equation, Move, ProofStep, add, all_shortest_paths, apply_equation,
    apply_rule, compare, distance, egg_prove, equivalent, frac, from_json, grade,
    greedy_hints, mul, neg, num, pretty, recheck_proof, rules, shortest_path, sub,
    to_json, var, verify_chain,
)
from eggregate.catalogue import BY_ID, CATALOGUE

X = var("x")
SOURCE = frac(mul(num(3), add(var("x"), num(0))), mul(num(3), num(1)))
TARGET = X
AVAILABLE = rules("add_zero_right", "frac_mul_cancel_left", "frac_one_denom", "mul_one_right")


# -- model / JSON -----------------------------------------------------------
def test_json_round_trip():
    assert from_json(to_json(SOURCE)) == SOURCE


def test_pretty():
    assert pretty(SOURCE) == "(3·(x + 0))/(3·1)"


def test_path_encoding_matches_thesis():
    # the inner sum x+0 sits at path [1,1] (numerator, then the mul's right child)
    assert pretty(SOURCE.at((1, 1))) == "x + 0"


# -- distance metric (Table 7) ---------------------------------------------
def test_distance_metric_matches_table7():
    s1 = frac(mul(num(3), var("x")), mul(num(3), num(1)))   # after step 0
    s2 = frac(var("x"), num(1))                              # after step 1
    assert distance(SOURCE, TARGET) == 8
    assert distance(s1, TARGET) == 6
    assert distance(s2, TARGET) == 2
    assert distance(TARGET, TARGET) == 0


# -- equivalence grading (Section 4.4 / B.3) -------------------------------
def test_grading_is_path_independent():
    # two different valid endpoints, both x -> both full marks
    assert grade(X, TARGET, rules=AVAILABLE) == 100
    assert grade(SOURCE, TARGET, rules=AVAILABLE) == 100  # source already in x's class


def test_grading_rejects_wrong_answer():
    assert grade(add(X, num(1)), TARGET, rules=AVAILABLE) == 0


def test_full_theory_equivalences():
    assert equivalent(add(X, num(0)), X)
    assert equivalent(neg(neg(X)), X)
    assert equivalent(sub(var("a"), var("b")), add(var("a"), neg(var("b"))))
    assert not equivalent(X, add(X, num(1)))


# -- hints (Table 8 + the MS3 improvement) ---------------------------------
def test_greedy_hints_match_table8():
    hints = greedy_hints(SOURCE, TARGET, AVAILABLE, k=3)
    ids = [h.rule_id for h in hints]
    dists = [distance(h.result, TARGET) for h in hints]
    assert ids == ["frac_mul_cancel_left", "add_zero_right", "mul_one_right"]
    assert dists == [4, 6, 6]


def test_multistep_path_reaches_goal():
    plan = shortest_path(SOURCE, TARGET, AVAILABLE)
    assert plan is not None and len(plan) == 3
    assert plan[-1].state == TARGET


def test_pedagogical_ordering_available():
    # MS3 can choose a plan that clears the +0 first (the thesis's example)
    plans = all_shortest_paths(SOURCE, TARGET, AVAILABLE)
    assert any(p[0].rule_id == "add_zero_right" for p in plans)


# -- step-local validator: Type A (rule application) -----------------------
def test_type_a_valid_by_construction():
    r = apply_rule(add(X, num(0)), BY_ID["add_zero_right"], ())
    assert r.ok and r.result == X


def test_type_a_reverse_requires_bidirectional():
    # add_zero_right is forward-only
    r = apply_rule(X, BY_ID["add_zero_right"], (), reverse=True)
    assert r.status == "invalid"


# -- guarded rules: the crux of soundness ----------------------------------
def test_guard_open_then_discharged():
    r = apply_rule(frac(X, X), BY_ID["frac_self_one"], ())
    assert r.status == "open"               # x/x = 1 needs x != 0
    r2 = apply_rule(frac(X, X), BY_ID["frac_self_one"], (),
                    assumptions=frozenset({Assumption("nonzero", X)}))
    assert r2.ok and r2.result == num(1)


def test_guard_violated_blocks_zero_over_zero():
    r = apply_rule(frac(num(0), num(0)), BY_ID["frac_self_one"], ())
    assert r.status == "invalid"            # 0/0 = 1 must be rejected


def test_oracle_stays_sound_on_symbolic_guard():
    # the e-graph must NOT bless x/x = 1 for unknown x, but 3/3 = 1 is fine
    assert not equivalent(frac(X, X), num(1))
    assert equivalent(frac(num(3), num(3)), num(1))


# -- step-local validator: Type B (Leibniz substitution) -------------------
def test_type_b_leibniz_substitution():
    eqn = Equation(add(X, num(0)), X)
    r = apply_equation(mul(add(X, num(0)), num(2)), eqn, (0,))
    assert r.ok and r.result == mul(X, num(2))


def test_type_b_rejects_non_matching_occurrence():
    eqn = Equation(add(X, num(0)), X)
    r = apply_equation(mul(X, num(2)), eqn, (0,))   # X is not (x+0)
    assert r.status == "invalid"


# -- whole-proof verification (no e-graph; transitivity over a sound chain) --
def test_verify_chain_replays_thesis_derivation():
    moves = [
        Move("A", (1, 1), rule=BY_ID["add_zero_right"]),
        Move("A", (),     rule=BY_ID["frac_mul_cancel_left"]),
        Move("A", (),     rule=BY_ID["frac_one_denom"]),
    ]
    report = verify_chain(SOURCE, moves, TARGET)
    assert report.valid and report.reached_goal and report.score == 100


# -- egg proof backend ------------------------------------------------------
def test_egg_prove_worked_example():
    proof = egg_prove(SOURCE, TARGET, AVAILABLE)
    assert proof is not None
    # the replayed chain genuinely reaches x (egg_prove asserts this internally)
    assert proof[-1].state == TARGET


def test_egg_prove_rejects_non_equivalent():
    assert egg_prove(add(X, num(1)), TARGET, AVAILABLE) is None


def test_egg_proves_symmetric_goal_bfs_cannot():
    # x == x+0 needs an "uphill" move; forward BFS can't, egg can
    assert shortest_path(X, add(X, num(0)), CATALOGUE) is None
    assert egg_prove(X, add(X, num(0)), CATALOGUE) is not None


def test_both_backends_agree_on_worked_example():
    c = compare(SOURCE, TARGET, AVAILABLE)
    assert c.bfs.found and c.egg.found and c.same_length


# -- semantic layer: sound disproof -----------------------------------------
def test_counterexample_disproves_false_equivalence():
    from eggregate import find_counterexample
    ce = find_counterexample(X, add(X, num(1)))      # x != x+1
    assert ce is not None
    assert find_counterexample(add(X, num(0)), X) is None   # x+0 == x, no witness


def test_division_by_zero_is_undefined_not_a_false_witness():
    from eggregate import evaluate
    from fractions import Fraction
    assert evaluate(frac(X, X), {"x": Fraction(0)}) is None   # 0/0 undefined
    assert evaluate(frac(num(6), num(6)), {}) == 1


# -- rule-library soundness fuzzer ------------------------------------------
def test_shipped_catalogue_is_sound():
    from eggregate import audit_catalogue
    assert all(a.sound for a in audit_catalogue(trials=400))


def test_fuzzer_catches_missing_guard():
    from eggregate import audit_rule
    from eggregate.catalogue import Rule, wild
    a = wild("a")
    bad = Rule("bad", "frac", frac(a, a), num(1))    # x/x = 1 with no x != 0
    res = audit_rule(bad, trials=400)
    assert not res.sound and res.counterexample is not None


def test_guards_are_load_bearing():
    from eggregate import audit_rule
    assert audit_rule(BY_ID["frac_mul_cancel_left"]).guard_necessary is True
    assert audit_rule(BY_ID["frac_self_one"]).guard_necessary is True


def test_audit_gate_passes_on_clean_catalogue():
    from eggregate.audit import main
    assert main(["200"]) == 0   # CI gate exits 0 when every rule is sound


# -- sample-solution-guided search ------------------------------------------
def _ref():
    from eggregate import reference_from_states
    s1 = frac(mul(num(3), X), mul(num(3), num(1)))
    return reference_from_states([SOURCE, s1, frac(X, num(1)), X])


def test_reference_validates_and_recovers_steps():
    from eggregate import check_reference
    chk = check_reference(_ref(), AVAILABLE)
    assert chk.ok
    assert [s.rule_id for s in chk.fine_steps] == [
        "add_zero_right", "frac_mul_cancel_left", "frac_one_denom"]


def test_guided_hint_follows_instructor_route_not_greedy():
    from eggregate import guided_hint, greedy_hints
    # greedy picks cancellation; the reference says clear the +0 first
    assert greedy_hints(SOURCE, X, AVAILABLE, k=1)[0].rule_id == "frac_mul_cancel_left"
    assert guided_hint(SOURCE, _ref(), AVAILABLE).step.rule_id == "add_zero_right"


def test_guided_hint_resteers_a_diverged_student():
    from eggregate import guided_hint
    diverged = frac(add(X, num(0)), num(1))      # student cancelled first
    h = guided_hint(diverged, _ref(), AVAILABLE)
    assert h.step is not None and h.step.rule_id == "add_zero_right"  # back onto the rail


def test_progress_is_structural_and_monotone_on_rail():
    from eggregate import progress
    ref = _ref()
    vals = [progress(s, ref) for s in ref.states]
    assert vals == sorted(vals) and vals[0] == 0.0 and vals[-1] == 1.0


# -- precomputed per-exercise e-graph ---------------------------------------
def _exg():
    from eggregate import precompute_exercise
    return precompute_exercise(SOURCE, X, AVAILABLE, reference=_ref(), bound=5)


def test_precompute_grades_in_class_forms_without_saturation():
    from eggregate import grade_submission
    exg = _exg()
    g = grade_submission(exg, frac(X, num(1)))      # an intermediate form
    assert g.score == 100 and g.equivalent and not g.saturated   # pure fast path


def test_precompute_grades_correct_and_wrong():
    from eggregate import grade_submission
    exg = _exg()
    assert grade_submission(exg, X).score == 100
    assert grade_submission(exg, X).proof == []     # target itself: 0-step proof
    assert grade_submission(exg, add(X, num(1))).score == 0


def test_precompute_matches_from_scratch_decision():
    from eggregate import grade_submission, decide_equivalence
    exg = _exg()
    for F in [SOURCE, frac(X, num(1)), add(X, num(1)), frac(add(X, num(0)), num(1))]:
        precomp = grade_submission(exg, F).equivalent
        scratch = decide_equivalence(F, X, AVAILABLE).outcome == "proven_equal"
        assert precomp == scratch


def test_egg_prove_does_not_crash_on_full_catalogue():
    # the rich-provenance replay bug must degrade gracefully, not raise
    p = egg_prove(SOURCE, X, CATALOGUE, bound=12)
    assert p is not None and p[-1].state == X


# -- grading service / protocol conformance ---------------------------------
def _gr(final=None, steps=None, rules=("add_zero_right", "frac_mul_cancel_left",
                                       "frac_one_denom", "mul_one_right")):
    from eggregate.model import to_json
    from eggregate.service import grade
    return grade({"protocol": "1.0", "exercise": {
        "mode": "transformation", "source": to_json(SOURCE), "target": to_json(X),
        "rules": list(rules)},
        "submission": {"final": final, "steps": steps}})


def test_service_target_form_is_full_marks():
    from eggregate.model import to_json
    r = _gr(final=to_json(X))
    assert r["outcome"] == "proven_equal" and r["score"] == 100 and r["certified"]


def test_service_unsimplified_equivalent_gets_partial_not_full():
    from eggregate.model import to_json, frac as F
    assert _gr(final=to_json(SOURCE))["score"] == 0        # source unchanged: no credit
    assert _gr(final=to_json(F(X, num(1))))["score"] == 75  # x/1: thesis distance formula


def test_service_wrong_answer_is_zero_with_witness():
    from eggregate.model import to_json
    r = _gr(final=to_json(add(X, num(1))))
    assert r["outcome"] == "proven_unequal" and r["score"] == 0 and r["witness"]


def test_service_rejects_fabricated_step_result():
    from eggregate.model import to_json
    bad = [{"rule": "add_zero_right", "path": [1, 1], "result": to_json(add(X, num(9)))}]
    r = _gr(steps=bad)
    assert r["outcome"] == "invalid_derivation" and r["score"] == 0


def test_service_valid_derivation_is_full_marks():
    from eggregate.model import to_json, frac as F, mul as M
    steps = [
        {"rule": "add_zero_right", "path": [1, 1],
         "result": to_json(F(M(num(3), X), M(num(3), num(1))))},
        {"rule": "frac_mul_cancel_left", "path": [], "result": to_json(F(X, num(1)))},
        {"rule": "frac_one_denom", "path": [], "result": to_json(X)},
    ]
    r = _gr(steps=steps)
    assert r["outcome"] == "proven_equal" and r["score"] == 100 and len(r["proof"]) == 3


# -- request-supplied ruleset (not hardcoded) -------------------------------
def test_rule_json_round_trips():
    from eggregate.catalogue import BY_ID, rule_from_json, rule_to_json
    for r in BY_ID.values():
        assert rule_from_json(rule_to_json(r)) == r


def test_service_grades_with_inline_ruleset():
    from eggregate.model import to_json, frac as F
    from eggregate.catalogue import BY_ID, rule_to_json
    from eggregate.service import grade
    ruleset = [rule_to_json(BY_ID[i]) for i in
               ("add_zero_right", "frac_mul_cancel_left", "frac_one_denom", "mul_one_right")]
    r = grade({"protocol": "1.0", "exercise": {
        "mode": "transformation", "source": to_json(SOURCE), "target": to_json(X),
        "ruleset": ruleset}, "submission": {"final": to_json(F(X, num(1)))}})
    assert r["outcome"] == "proven_equal" and r["score"] == 75


def test_service_audits_unsound_instructor_rule():
    from eggregate.model import to_json
    from eggregate.catalogue import Rule, rule_to_json, wild
    from eggregate.service import grade, RequestError
    a = wild("a")
    bad = Rule("xx_to_1", "frac", frac(a, a), num(1))   # x/x=1 without x!=0
    try:
        grade({"protocol": "1.0", "exercise": {
            "mode": "transformation", "source": to_json(SOURCE), "target": to_json(X),
            "ruleset": [rule_to_json(bad)], "options": {"audit_rules": True}},
            "submission": {"final": to_json(X)}})
        assert False, "unsound rule was not rejected"
    except RequestError as e:
        assert "unsound" in str(e)


# -- robust three-valued decision -------------------------------------------
def test_robust_grade_certifies_correct():
    score, v = __import__("eggregate", fromlist=["grade_robust"]).grade_robust(
        SOURCE, TARGET, AVAILABLE)
    assert score == 100 and v.outcome == "proven_equal" and recheck_proof(SOURCE, v.proof)


def test_robust_grade_disproves_wrong_with_witness():
    from eggregate import grade_robust
    score, v = grade_robust(SOURCE, add(X, num(1)), AVAILABLE)
    assert score == 0 and v.outcome == "proven_unequal" and v.witness is not None


def test_recheck_rejects_tampered_proof():
    # a "proof" whose stated result doesn't follow from the rule must be rejected
    from eggregate import egg_prove
    proof = egg_prove(SOURCE, TARGET, AVAILABLE)
    tampered = list(proof)
    tampered[-1] = ProofStep(proof[-1].rule_id, proof[-1].forward,
                             proof[-1].path, add(X, num(99)))   # lie about the result
    assert recheck_proof(SOURCE, proof)
    assert not recheck_proof(SOURCE, tampered)


if __name__ == "__main__":
    fns = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    for fn in fns:
        fn()
        print(f"ok  {fn.__name__}")
    print(f"\n{len(fns)} tests passed")
