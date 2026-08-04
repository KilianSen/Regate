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


def test_path_encoding_alphabetical_slots():
    # the inner sum x+0 sits at path [1,1] (numerator, then the mul's right child)
    assert pretty(SOURCE.at((1, 1))) == "x + 0"


# -- distance metric --------------------------------------------------------
def test_distance_metric_matches_table7():
    s1 = frac(mul(num(3), var("x")), mul(num(3), num(1)))   # after step 0
    s2 = frac(var("x"), num(1))                              # after step 1
    assert distance(SOURCE, TARGET) == 8
    assert distance(s1, TARGET) == 6
    assert distance(s2, TARGET) == 2
    assert distance(TARGET, TARGET) == 0


# -- equivalence grading ----------------------------------------------------
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


# -- hints (+ the MS3 improvement) ------------------------------------------
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
    # MS3 can choose a plan that clears the +0 first
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
def test_verify_chain_replays_reference_derivation():
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
    assert _gr(final=to_json(F(X, num(1))))["score"] == 75  # x/1: distance formula


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


# -- grown catalogue: negation + fraction rules (Tier 3) --------------------
def test_new_negation_and_fraction_rules_extend_reach():
    A, B, C, D = var("a"), var("b"), var("c"), var("d")
    y = var("y")
    assert equivalent(neg(add(X, y)), add(neg(X), neg(y)))            # neg_add
    assert equivalent(mul(neg(X), y), neg(mul(X, y)))                 # mul_neg_left
    assert equivalent(add(frac(X, C), frac(y, C)), frac(add(X, y), C))  # frac_add_same_denom
    assert equivalent(mul(frac(A, B), frac(C, D)), frac(mul(A, C), mul(B, D)))  # frac_mul


def test_grown_catalogue_still_sound():
    from eggregate import audit_catalogue
    audits = audit_catalogue(trials=400)
    assert len(audits) == 29 and all(a.sound for a in audits)


# -- AC normalisation (Tier 3) ----------------------------------------------
def test_ac_normalize_canonicalises_commutative_associative():
    from eggregate import ac_normalize
    y, z = var("y"), var("z")
    assert ac_normalize(add(y, X)) == ac_normalize(add(X, y))                 # commutativity
    assert ac_normalize(add(add(X, y), z)) == ac_normalize(add(X, add(y, z)))  # associativity
    assert ac_normalize(add(X, y)) != ac_normalize(add(X, z))                 # genuinely different


def test_service_ac_normalization_accepts_commuted_target():
    from eggregate.model import to_json
    from eggregate.service import grade
    yy = var("y")
    src, tgt = add(X, yy), add(yy, X)   # x+y  vs target  y+x, no commutativity rule given

    def run(ac):
        return grade({"protocol": "1.0", "exercise": {
            "mode": "transformation", "source": to_json(src), "target": to_json(tgt),
            "rules": ["add_zero_right"], "options": {"ac_normalization": ac}},
            "submission": {"final": to_json(src)}})

    assert run(False)["outcome"] != "proven_equal"          # can't prove without comm
    r = run(True)
    assert r["outcome"] == "proven_equal" and r["score"] == 100 and r["certified"]


def test_service_ac_still_disproves_wrong_answer():
    from eggregate.model import to_json
    from eggregate.service import grade
    yy = var("y")
    r = grade({"protocol": "1.0", "exercise": {
        "mode": "transformation", "source": to_json(add(X, yy)), "target": to_json(add(X, yy)),
        "rules": "ALL", "options": {"ac_normalization": True}},
        "submission": {"final": to_json(add(X, num(1)))}})   # x+1 is not x+y
    assert r["outcome"] == "proven_unequal" and r["score"] == 0


# -- regression tests for the audit-hardening (previously unpinned) ----------
# Each of these fails if the corresponding fix is reverted. They pin: the three
# uncaught-exception paths that used to become HTTP 500 / CLI exit 1, and the
# assumptions threading that used to be dropped on every path but `steps`.
def _svc(request):
    from eggregate.service import grade as _g
    return _g(request)


def _err(request):
    """Return the RequestError message, or None if grade() did not raise it."""
    from eggregate.service import RequestError
    try:
        _svc(request)
        return None
    except RequestError as e:
        return str(e)
    # any *other* exception propagates: that is the bug these tests guard against.


def test_reverse_guarded_rule_does_not_crash():
    # A bidirectional guarded rule applied in reverse: the RHS pattern (`1`) does
    # not bind the guarded var `a`, so the guard is undecidable. Must be a clean
    # invalid step, never a KeyError escaping as a 500.
    from eggregate.model import to_json
    wa = {"type": "wild", "value": "a"}
    rs = [{"id": "self_one", "owner": "frac",
           "lhs": {"type": "frac", "slots": {"denominator": [wa], "numerator": [wa]}},
           "rhs": {"type": "number", "value": "1"}, "bidirectional": True,
           "conditions": [{"kind": "nonzero", "var": "a"}]}]
    req = {"protocol": "1.0", "exercise": {
        "mode": "transformation", "source": {"type": "number", "value": "1"},
        "target": to_json(frac(X, X)), "ruleset": rs,
        "assumptions": [{"kind": "nonzero", "value": to_json(X)}]},
        "submission": {"steps": [{"rule": "self_one", "path": [], "direction": "reverse",
                                  "kind": "A", "result": to_json(frac(X, X))}]}}
    r = _svc(req)      # must not raise
    assert r["outcome"] == "invalid_derivation" and not r["certified"]


def test_kind_b_step_missing_equation_is_400():
    from eggregate.model import to_json
    msg = _err({"protocol": "1.0", "exercise": {
        "mode": "transformation", "source": to_json(X), "target": to_json(X), "rules": "ALL"},
        "submission": {"steps": [{"kind": "B", "path": []}]}})
    assert msg is not None and "equation" in msg


def test_malformed_mathnode_is_400_not_500():
    msg = _err({"protocol": "1.0", "exercise": {
        "mode": "transformation", "source": {"type": "bogus"},
        "target": {"type": "variable", "value": "x"}, "rules": "ALL"},
        "submission": {"final": {"type": "variable", "value": "x"}}})
    assert msg is not None and "malformed" in msg


def test_pow_in_transformation_mode_does_not_crash():
    # `pow`/`succ` are legal MathNodes (induction uses them). Reaching the ℚ
    # evaluator via decide_equivalence used to raise ValueError -> 500.
    pw = {"type": "pow", "slots": {"base": [{"type": "variable", "value": "a"}],
                                   "exponent": [{"type": "number", "value": "1"}]}}
    r = _svc({"protocol": "1.0", "exercise": {
        "mode": "transformation", "source": pw, "target": pw, "rules": "ALL"},
        "submission": {"final": {"type": "variable", "value": "a"}}})
    assert r["outcome"] == "unknown" and r["score"] is None      # honest, not a crash


def test_pow_is_evaluated_for_a_sound_disproof():
    # a^2 is not a: the evaluator must now compute pow to find the counterexample.
    pw = {"type": "pow", "slots": {"base": [{"type": "variable", "value": "a"}],
                                   "exponent": [{"type": "number", "value": "2"}]}}
    r = _svc({"protocol": "1.0", "exercise": {
        "mode": "transformation", "source": pw, "target": pw, "rules": "ALL"},
        "submission": {"final": {"type": "variable", "value": "a"}}})
    assert r["outcome"] == "proven_unequal" and r["witness"] is not None


def test_assumption_certifies_a_guarded_equation():
    # x/x = 1 holds only under x != 0. With the assumption declared, the equation
    # certifies; without it, the grader must stay honestly inconclusive. This pins
    # assumptions reaching decide_equivalence (they used to be dropped there).
    from eggregate.model import to_json
    eq_node = {"type": "eq", "slots": {"left": [to_json(frac(X, X))],
                                       "right": [{"type": "number", "value": "1"}]}}
    base = {"protocol": "1.0", "exercise": {
        "mode": "equation", "source": eq_node, "target": None, "rules": ["frac_self_one"]},
        "submission": {"final": eq_node}}
    with_assump = {**base, "exercise": {**base["exercise"],
                   "assumptions": [{"kind": "nonzero", "value": to_json(X)}]}}
    assert _svc(with_assump)["outcome"] == "proven_equal"
    assert _svc(base)["outcome"] == "unknown"


def test_declared_nonzero_is_not_a_counterexample():
    # Under x != 0, x = 0 must be excluded from the counterexample search — else a
    # true-under-assumption identity is wrongly reported proven_unequal.
    from eggregate.model import to_json
    src = frac(mul(X, var("b")), mul(X, var("a")))
    r = _svc({"protocol": "1.0", "exercise": {
        "mode": "transformation", "source": to_json(src), "target": to_json(frac(var("b"), var("a"))),
        "rules": ["frac_mul_cancel_left"],
        "assumptions": [{"kind": "nonzero", "value": to_json(X)}]},
        "submission": {"final": to_json(frac(var("b"), var("a")))}})
    assert r["outcome"] == "proven_equal" and r["witness"] is None


def test_verify_rules_rejects_unsound_inline_rule():
    # options.verify_rules re-establishes the ruleset warrant: an inline rule that
    # lies (a*b -> b) is rejected with a counterexample, on the induction path too.
    from eggregate.model import to_json
    bad = [{"id": "drop_left", "owner": "mul",
            "lhs": {"type": "mul", "slots": {"left": [{"type": "wild", "value": "a"}],
                                             "right": [{"type": "wild", "value": "b"}]}},
            "rhs": {"type": "wild", "value": "b"}, "bidirectional": False, "conditions": []}]
    msg = _err({"protocol": "1.0", "exercise": {
        "mode": "transformation", "source": to_json(X), "target": to_json(X),
        "ruleset": bad, "options": {"verify_rules": True}},
        "submission": {"final": to_json(X)}})
    assert msg is not None and "drop_left" in msg
    # ...and trusted by default: the same request without the flag does not raise.
    assert _err({"protocol": "1.0", "exercise": {
        "mode": "transformation", "source": to_json(X), "target": to_json(X), "ruleset": bad},
        "submission": {"final": to_json(X)}}) is None


# -- `apply`: n-ary named function application (protocol 1.1) ---------------
def _wild(n):
    from eggregate.model import MathNode
    return MathNode("wild", n)


# max(a, b) = max(b, a) as a *definition* (data, not backend code): this is the
# whole point of `apply` -- a host adds a binary operator by sending a node plus
# its definitions, with no backend change.
def _max_comm_def():
    from eggregate.model import apply as ap, to_json
    return {"id": "max_comm", "owner": "max",
            "lhs": to_json(ap("max", _wild("a"), _wild("b"))),
            "rhs": to_json(ap("max", _wild("b"), _wild("a"))),
            "bidirectional": True, "conditions": []}


def test_apply_json_round_trips_and_prints():
    from eggregate.model import apply as ap, to_json, from_json as fj, pretty as pp
    n = ap("fact_aux", var("x"), var("n"))
    j = to_json(n)
    assert j == {"type": "apply", "value": "fact_aux", "slots": {"args": [
        {"type": "variable", "value": "x"}, {"type": "variable", "value": "n"}]}}
    assert fj(j) == n
    assert pp(n) == "fact_aux(x, n)"
    # nullary (a constructor like `nil`) and the flat-child path encoding
    assert fj(to_json(ap("nil"))) == ap("nil")
    assert n.at((1,)) == var("n")


def test_apply_name_and_arity_are_part_of_identity():
    from eggregate.model import apply as ap
    from eggregate.matching import match
    assert ap("f", X) != ap("g", X)
    assert match(ap("f", _wild("a")), ap("f", X)) == {"a": X}
    assert match(ap("f", _wild("a")), ap("g", X)) is None          # name differs
    assert match(ap("f", _wild("a")), ap("f", X, X)) is None       # arity differs


def test_apply_malformed_is_a_400_not_a_500():
    from eggregate.model import to_json
    # missing function name, and a non-list args slot
    for bad in ({"type": "apply", "slots": {"args": []}},
                {"type": "apply", "value": "f", "slots": {"args": {"a": 1}}},
                {"type": "apply", "value": "f"}):
        msg = _err({"protocol": "1.1", "exercise": {
            "mode": "transformation", "source": bad, "target": to_json(X),
            "ruleset": []}, "submission": {"final": to_json(X)}})
        assert msg is not None and "exercise.source" in msg


def test_apply_derivation_is_step_validated():
    from eggregate.model import apply as ap, to_json
    src, tgt = to_json(ap("max", X, var("y"))), to_json(ap("max", var("y"), X))
    r = _svc({"protocol": "1.1", "exercise": {
        "mode": "transformation", "source": src, "target": tgt,
        "ruleset": [], "definitions": [_max_comm_def()]},
        "submission": {"steps": [{"rule": "max_comm", "path": [], "kind": "A",
                                  "result": tgt}]}})
    assert r["outcome"] == "proven_equal" and r["score"] == 100 and r["certified"]
    assert r["proof"] == [{"rule": "max_comm", "path": [], "direction": "forward",
                           "state": tgt}]


def test_apply_bogus_derivation_step_is_invalid_not_a_crash():
    from eggregate.model import apply as ap, to_json
    src = to_json(ap("max", X, var("y")))
    r = _svc({"protocol": "1.1", "exercise": {
        "mode": "transformation", "source": src, "target": to_json(X),
        "ruleset": [], "definitions": [_max_comm_def()]},
        "submission": {"steps": [{"rule": "max_comm", "path": [], "kind": "A",
                                  "result": to_json(X)}]}})   # fabricated result
    assert r["outcome"] == "invalid_derivation" and r["score"] == 0


def test_apply_endpoint_equivalence_reaches_the_oracle():
    # An `apply` term now compiles to egglog (one constructor per arity, the name
    # carried as a String), so endpoint grading works rather than 400-ing.
    from eggregate.model import apply as ap, to_json
    src = to_json(ap("max", add(X, num(0)), var("y")))
    tgt = to_json(ap("max", X, var("y")))
    r = _svc({"protocol": "1.1", "exercise": {
        "mode": "transformation", "source": src, "target": tgt,
        "rules": ["add_zero_right"]}, "submission": {"final": src}})
    assert r["outcome"] == "proven_equal" and r["certified"] and r["proof"] is not None


def test_apply_unfoldable_definition_is_proven_equal():
    from eggregate.model import apply as ap, to_json
    # double(a) -> a + a, cited by definition id in a derivation
    d = {"id": "double_def", "owner": "double",
         "lhs": to_json(ap("double", _wild("a"))),
         "rhs": to_json(add(_wild("a"), _wild("a"))),
         "bidirectional": True, "conditions": []}
    r = _svc({"protocol": "1.1", "exercise": {
        "mode": "transformation", "source": to_json(ap("double", X)),
        "target": to_json(add(X, X)), "ruleset": [], "definitions": [d]},
        "submission": {"final": to_json(ap("double", X))}})
    assert r["outcome"] == "proven_equal" and r["certified"]


def test_apply_never_fabricates_a_counterexample():
    """THE soundness invariant: the ℚ evaluator has no value for an uninterpreted
    `apply`, so it must answer "cannot decide", never `proven_unequal`."""
    from eggregate.model import apply as ap, to_json
    from eggregate.semantics import evaluate, find_counterexample, is_evaluable
    from fractions import Fraction
    f = ap("f", X)
    assert not is_evaluable(f) and not is_evaluable(add(f, num(1)))
    try:
        evaluate(f, {"x": Fraction(1)})
        raise AssertionError("evaluate must refuse an uninterpreted apply")
    except ValueError:
        pass
    # f(x) vs f(x)+1 are genuinely unequal, but we cannot witness it -> None.
    assert find_counterexample(f, add(f, num(1)), 200) is None
    r = _svc({"protocol": "1.1", "exercise": {
        "mode": "transformation", "source": to_json(f),
        "target": to_json(add(f, num(1))), "ruleset": []},
        "submission": {"final": to_json(f)}})
    assert r["outcome"] == "unknown" and r["score"] is None and r["witness"] is None


def test_apply_rule_cannot_be_fuzz_verified():
    # verify_rules asks us to re-establish the warrant; the ℚ fuzzer cannot even
    # evaluate an `apply`, so we decline (400) rather than report it as verified.
    from eggregate.model import to_json
    from eggregate.audit import audit_rule
    from eggregate.rule import rule_from_json
    d = _max_comm_def()
    a = audit_rule(rule_from_json(d))
    assert a.sound and a.fuzzable is False       # "not checked", not "checked ok"
    msg = _err({"protocol": "1.1", "exercise": {
        "mode": "transformation", "source": to_json(X), "target": to_json(X),
        "ruleset": [d], "options": {"verify_rules": True}},
        "submission": {"final": to_json(X)}})
    assert msg is not None and "max_comm" in msg
    # ...but as a *definition* it is trusted by declaration, so no error.
    assert _err({"protocol": "1.1", "exercise": {
        "mode": "transformation", "source": to_json(X), "target": to_json(X),
        "ruleset": [], "definitions": [d], "options": {"verify_rules": True}},
        "submission": {"final": to_json(X)}}) is None


def test_apply_over_max_arity_declines_instead_of_crashing():
    from eggregate.model import apply as ap, to_json
    from eggregate.backend import MAX_APPLY_ARITY, equivalent as eqv
    wide = ap("wide", *([X] * (MAX_APPLY_ARITY + 2)))
    assert eqv(wide, X) is False                       # oracle declines, no raise
    r = _svc({"protocol": "1.1", "exercise": {
        "mode": "transformation", "source": to_json(wide), "target": to_json(X),
        "ruleset": []}, "submission": {"final": to_json(wide)}})
    assert r["outcome"] == "unknown" and r["score"] is None


def test_datatype_induction_declines_instead_of_grading_zero():
    # Now that `apply` parses, a list/tree induction reaches the ℕ-only obligation
    # generator. Grading it there would report a VALID derivation as
    # `invalid_derivation` — so decline (unknown), per the protocol's second
    # conformant decline.
    from eggregate.model import apply as ap, to_json, eq as EQ
    goal = EQ(ap("len", var("l")), ap("len", var("l")))
    r = _svc({"protocol": "1.1", "exercise": {
        "mode": "induction", "goal": to_json(goal), "inductionVar": "l",
        "datatype": {"name": "Lst", "constructors": [
            {"name": "nil", "fields": []},
            {"name": "cons", "fields": [{"name": "h", "sort": "int"},
                                        {"name": "t", "sort": "Lst"}]}]},
        "ruleset": []},
        "submission": {"base": {"steps": []}, "step": {"steps": []}}})
    assert r["outcome"] == "unknown" and r["score"] is None and not r["certified"]
    assert "Lst" in r["feedback"]


def test_generalized_ih_declines_instead_of_grading_zero():
    # IH `f(x, n) = g(x, n)` cited at the SHIFTED accumulator `x·S(n)`: sound under
    # the accumulator-universal IH, which this backend does not model. It must not
    # be scored 0 as an out-of-scope substitution.
    from eggregate.model import apply as ap, to_json, succ as S, eq as EQ
    goal = EQ(ap("f", X, var("n")), ap("g", X, var("n")))
    shifted = mul(X, S(var("n")))
    b_step = {"kind": "B", "path": [],
              "equation": [to_json(ap("f", shifted, var("n"))),
                           to_json(ap("g", shifted, var("n")))]}
    r = _svc({"protocol": "1.1", "exercise": {
        "mode": "induction", "goal": to_json(goal), "inductionVar": "n",
        "ruleset": []},
        "submission": {"base": {"steps": []}, "step": {"steps": [b_step]}}})
    assert r["outcome"] == "unknown" and r["score"] is None
    assert r["meta"]["induction"]["declined"] == "generalized_ih"
    # The circular use of the IH at `S n` is NOT a generalized instance and stays
    # an invalid derivation (fixture 20's guarantee).
    circ = {"kind": "B", "path": [],
            "equation": [to_json(ap("f", X, S(var("n")))),
                         to_json(ap("g", X, S(var("n"))))]}
    r2 = _svc({"protocol": "1.1", "exercise": {
        "mode": "induction", "goal": to_json(goal), "inductionVar": "n",
        "ruleset": []},
        "submission": {"base": {"steps": []}, "step": {"steps": [circ]}}})
    assert r2["outcome"] == "invalid_derivation" and r2["score"] == 0


def test_apply_in_induction_definitions_still_grades():
    from eggregate.model import apply as ap, to_json, succ as S, eq as EQ
    # sum(0) = 0 ; the base obligation closes by the definition rule alone.
    goal = EQ(ap("sum", var("n")), ap("sum", var("n")))
    d = {"id": "sum_refl", "owner": "sum",
         "lhs": to_json(ap("sum", _wild("a"))), "rhs": to_json(ap("sum", _wild("a"))),
         "bidirectional": False, "conditions": []}
    r = _svc({"protocol": "1.1", "exercise": {
        "mode": "induction", "goal": to_json(goal), "inductionVar": "n",
        "ruleset": [], "definitions": [d]},
        "submission": {"base": {"steps": []}, "step": {"steps": []}}})
    assert r["outcome"] == "equal_no_certificate" and r["score"] is None


if __name__ == "__main__":
    fns = [v for k, v in sorted(globals().items()) if k.startswith("test_")]
    for fn in fns:
        fn()
        print(f"ok  {fn.__name__}")
    print(f"\n{len(fns)} tests passed")
