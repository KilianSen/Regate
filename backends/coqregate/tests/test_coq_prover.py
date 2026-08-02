from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import coq_induction
import coq_prover
import grade


# --- MathNode builders (the protocol JSON shape) ----------------------------
def num(v): return {"type": "number", "value": str(v)}
def vr(v): return {"type": "variable", "value": v}
def wd(v): return {"type": "wild", "value": v}
def b(t, l, r): return {"type": t, "slots": {"left": [l], "right": [r]}}
def mul(l, r): return b("mul", l, r)
def add(l, r): return b("add", l, r)
def eq(l, r): return b("eq", l, r)
def succ(x): return {"type": "succ", "slots": {"inner": [x]}}
def powr(base, exp): return {"type": "pow", "slots": {"base": [base], "exponent": [exp]}}
def drule(rid, lhs, rhs): return {"id": rid, "lhs": lhs, "rhs": rhs, "bidirectional": False, "conditions": []}

DEFS = [drule("pow_zero", powr(wd("a"), num(0)), num(1)),
        drule("pow_succ", powr(wd("a"), succ(wd("n"))), mul(wd("a"), powr(wd("a"), wd("n"))))]


def ex(goal, var="n"):
    return {"mode": "induction", "goal": goal, "inductionVar": var, "definitions": DEFS}


# --- a stub Coq: succeeds on a configurable predicate over the source --------
class FakeCoq:
    def __init__(self, accept):
        self.accept = accept
        self.calls: list[str] = []

    def __call__(self, source: str):
        self.calls.append(source)
        return (True, "") if self.accept(source) else (False, "Error: unsolved goal")


def _install(accept):
    coq_prover._CACHE.clear()
    coq_induction._CACHE.clear()
    coq_induction._RULE_CACHE.clear()
    coq_prover.coq_available = lambda: True        # type: ignore[assignment]
    fake = FakeCoq(accept)
    coq_prover.check_source = fake                  # type: ignore[assignment]
    return fake


# --- translation / typing ---------------------------------------------------
def test_term_translation_q():
    assert coq_induction._term(vr("a"), "Q") == "a"
    assert coq_induction._term(num(1), "Q") == "1"
    assert coq_induction._term(add(vr("a"), vr("b")), "Q") == "(a + b)"
    assert coq_induction._term(mul(vr("a"), vr("b")), "Q") == "(a * b)"


def test_term_pow_forces_nat_scope_on_exponent():
    # exponent must be wrapped in (...)%nat; the base stays in ℚ scope.
    t = coq_induction._term(powr(vr("a"), add(vr("m"), vr("n"))), "Q")
    assert t == "(pw a ((m + n))%nat)"


def test_infer_types_exponent_as_nat():
    env: dict[str, str] = {}
    coq_induction._infer(eq(powr(vr("a"), vr("n")), num(1)), "Q", env)
    assert env["a"] == "Q" and env["n"] == "N"


def test_infer_rejects_mixed_use():
    env: dict[str, str] = {}
    # x used as a ℚ base AND as a ℕ exponent -> contradiction.
    try:
        coq_induction._infer(eq(powr(vr("x"), vr("x")), num(1)), "Q", env)
        assert False, "expected InductionError"
    except coq_induction.InductionError:
        pass


def test_build_source_shape():
    src = coq_induction.build_source(ex(eq(powr(num(1), vr("n")), num(1))))
    assert "Fixpoint pw (a : Q) (n : nat) : Q" in src
    assert "| O => 1" in src
    assert "| S k => (a * (pw a (k)%nat))" in src   # succ var renamed to canonical `a`/`k`
    assert "Theorem regate_induction : forall (n : nat), (pw 1 (n)%nat) == 1." in src
    assert "induction n as [| k ih]." in src
    # We prove Qeq (`==`), not Leibniz `=` — see the module docstring.
    assert "== 1." in src


def test_build_source_renames_distinct_def_vars():
    # definitions that use different wildcard names must still produce a
    # well-formed Fixpoint with the canonical binders `a`/`k`.
    defs = [drule("pz", powr(wd("x"), num(0)), num(1)),
            drule("ps", powr(wd("y"), succ(wd("m"))), mul(wd("y"), powr(wd("y"), wd("m"))))]
    e = {"mode": "induction", "goal": eq(powr(num(1), vr("n")), num(1)),
         "inductionVar": "n", "definitions": defs}
    src = coq_induction.build_source(e)
    assert "| S k => (a * (pw a (k)%nat))" in src


def test_build_source_requires_eq_goal():
    try:
        coq_induction.build_source({"mode": "induction", "goal": num(1),
                                    "inductionVar": "n", "definitions": DEFS})
        assert False
    except coq_induction.InductionError:
        pass


def test_build_source_requires_nat_induction_var():
    # inducting over a ℚ variable is outside the fragment.
    try:
        coq_induction.build_source(ex(eq(add(vr("a"), num(1)), vr("a")), var="a"))
        assert False
    except coq_induction.InductionError:
        pass


# --- certify wiring (stubbed kernel) ----------------------------------------
def test_certify_accepts():
    _install(lambda src: True)
    res = coq_induction.certify(ex(eq(powr(num(1), vr("n")), num(1))))
    assert res.certified and res.method == "induction"


def test_certify_rejects():
    _install(lambda src: False)
    res = coq_induction.certify(ex(eq(powr(num(1), vr("n")), num(1))))
    assert not res.certified and res.method == "rejected"


def test_certify_untranslatable():
    _install(lambda src: True)
    res = coq_induction.certify({"mode": "induction", "goal": num(1),
                                 "inductionVar": "n", "definitions": DEFS})
    assert not res.certified and res.method == "untranslatable"


def test_certify_unavailable():
    coq_prover._CACHE.clear()
    coq_induction._CACHE.clear()
    coq_prover.coq_available = lambda: False        # type: ignore[assignment]
    res = coq_induction.certify(ex(eq(powr(num(1), vr("n")), num(1))))
    assert not res.certified and res.method == "unavailable"


def test_certify_caches_by_source():
    fake = _install(lambda src: True)
    g = ex(eq(powr(num(1), vr("n")), num(1)))
    coq_induction.certify(g)
    coq_induction.certify(g)
    assert len(fake.calls) == 1                       # checked once, reused


# --- grade.py wiring: STRICT rule-instance grading (symbolic) + kernel backstop -
# A real valid proof of `1ⁿ = 1`: pow_zero closes the base; pow_succ + the IH +
# mul_one_left close the step. The rules are matched against the transmitted
# ruleset (mul_one_left) + definitions (pow_zero/pow_succ).
GOAL_1N = eq(powr(num(1), vr("n")), num(1))
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
    e = ex(GOAL_1N)
    if ruleset is not None:
        e["ruleset"] = ruleset
    return {"protocol": "1.0", "exercise": e, "submission": submission}


def test_grade_induction_certified():
    _install(lambda src: True)                         # kernel backstop certifies the goal
    resp = grade.grade(_ind_req(_sub(VALID_BASE, VALID_STEP)))
    assert resp["outcome"] == "proven_equal" and resp["certified"] and resp["score"] == 100
    assert resp["meta"]["induction"]["status"] == "certified"


def test_certified_carries_a_recheckable_proof():
    # The protocol: `certified: true` must carry a proof the caller can re-verify.
    _install(lambda src: True)
    resp = grade.grade(_ind_req(_sub(VALID_BASE, VALID_STEP)))
    proof = resp["proof"]
    assert proof and proof[0]["engine"] == "coq"
    assert f"Theorem {coq_induction.THEOREM}" in proof[0]["source"] and "Qed." in proof[0]["source"]


UNSOUND = [{"id": "drop_left", "lhs": mul(wd("a"), wd("b")), "rhs": wd("b"),
            "bidirectional": False, "conditions": []}]


def _unsound_step():
    step = [dict(s) for s in VALID_STEP]
    step[2] = dict(step[2], rule="drop_left")
    return step


def _verify(req):
    req["exercise"]["options"] = {"verify_rules": True}
    return req


def test_ruleset_is_trusted_by_default():
    # Regate's premise: the ruleset is authored and formally validated upstream, so
    # the grading path takes the caller's warrant and does not re-prove it. No coqc
    # run is spent on the rules — only on the induction goal.
    fake = _install(lambda src: True)
    resp = grade.grade(_ind_req(_sub(VALID_BASE, VALID_STEP)))
    assert resp["outcome"] == "proven_equal" and resp["certified"]
    assert resp["meta"]["ruleset"]["mul_one_left"]["method"] == "trusted"
    assert all(f"Theorem {coq_induction.RULE_THEOREM}" not in s for s in fake.calls)


def test_verify_rules_rejects_an_unsound_rule():
    # With verify_rules on, the warrant is re-established here. The Coq kernel
    # certifies the GOAL (1ⁿ = 1, true) but rejects the FALSE rule `a·b = b` the
    # step cites — so the derivation is `unknown`, inconclusive, not a wrong answer.
    # Without this, correctly applying a false rule to reach a true goal certifies.
    _install(lambda src: f"Theorem {coq_induction.RULE_THEOREM}" not in src)
    resp = grade.grade(_verify(_ind_req(_sub(VALID_BASE, _unsound_step()), ruleset=UNSOUND)))
    assert resp["outcome"] == "unknown" and resp["score"] is None and not resp["certified"]
    assert resp["meta"]["ruleset"]["drop_left"]["proven"] is False


def test_verify_rules_still_certifies_a_sound_rule():
    _install(lambda src: True)
    resp = grade.grade(_verify(_ind_req(_sub(VALID_BASE, VALID_STEP))))
    assert resp["outcome"] == "proven_equal" and resp["certified"]
    assert resp["meta"]["ruleset"]["mul_one_left"]["method"] == "ring"


def test_carried_proof_field_is_ignored():
    # Regate does not run a caller-supplied proof script (injection surface; rule
    # soundness is the caller's upstream job). A `proof` on a rule must never reach
    # coqc — the rule is proven only by the automatic tactic, or not at all.
    fake = _install(lambda src: True)
    with_proof = [dict(RULESET[0], proof="admit. Admitted. Theorem t2 : True. Proof. exact I")]
    resp = grade.grade(_verify(_ind_req(_sub(VALID_BASE, VALID_STEP), ruleset=with_proof)))
    assert resp["meta"]["ruleset"]["mul_one_left"]["method"] == "ring"   # auto, never "carried"
    assert all("Admitted" not in s and "t2" not in s for s in fake.calls)  # payload never emitted


def test_injected_false_rule_is_not_proven():
    # A FALSE rule (a -> a+1) shipping an injection payload must not be provable, even
    # against a kernel stub that would accept any decoy file. With carried proofs
    # gone, prove_rule only auto-proves the real (false) theorem, which fails.
    from coq_induction import prove_rule, _RULE_CACHE
    _install(lambda src: "0" not in src and "1" not in src)   # reject the real false goal
    _RULE_CACHE.clear()
    evil = {"id": "evil", "lhs": vr("a"), "rhs": add(vr("a"), num(1)), "conditions": [],
            "proof": "admit. Admitted. Theorem t2 : True. Proof. exact I"}
    res = prove_rule(evil, [])
    assert res.proven is False and res.method == "rejected"


def test_grade_induction_invalid_wrong_result():
    _install(lambda src: True)                         # symbolic check rejects before the backstop
    bad = [dict(VALID_BASE[0], result=eq(num(1), num(2)))]   # pow_zero gives 1=1, not 1=2
    resp = grade.grade(_ind_req(_sub(bad, VALID_STEP)))
    assert resp["outcome"] == "invalid_derivation" and resp["score"] == 0 and not resp["certified"]


def test_grade_induction_invalid_wrong_rule():
    _install(lambda src: True)
    bad = [dict(VALID_BASE[0], rule="pow_succ")]        # pow_succ does not match pow(1,0) — strict
    resp = grade.grade(_ind_req(_sub(bad, VALID_STEP)))
    assert resp["outcome"] == "invalid_derivation" and resp["score"] == 0


def test_grade_induction_unknown_when_unattempted():
    _install(lambda src: True)                         # no submission -> never an auto-pass
    resp = grade.grade({"protocol": "1.0", "exercise": ex(GOAL_1N)})
    assert resp["outcome"] == "unknown" and resp["score"] is None and not resp["certified"]


def test_grade_induction_unknown_when_backstop_rejects():
    _install(lambda src: False)                        # steps valid, but the kernel won't certify the goal
    resp = grade.grade(_ind_req(_sub(VALID_BASE, VALID_STEP)))
    assert resp["outcome"] == "unknown" and resp["score"] is None and not resp["certified"]


def test_grade_induction_unknown_when_unavailable():
    coq_prover._CACHE.clear()
    coq_induction._CACHE.clear()
    coq_prover.coq_available = lambda: False         # type: ignore[assignment]
    resp = grade.grade(_ind_req(_sub(VALID_BASE, VALID_STEP)))
    assert resp["outcome"] == "unknown" and resp["score"] is None


def test_ac_matching_commutative():
    # `mul_one_left` is `1·a → a`; applied to `x·1` (the 1 on the *other* side) it
    # only matches modulo commutativity. AC off ⇒ no match (invalid); AC on ⇒ closes.
    import step_check as sc
    # `proven=True`: this test is about AC matching, not about the kernel's verdict
    # on the rule. An unproven rule is uncertifiable before matching is even tried.
    rules = {"mul_one_left": sc.Rule("mul_one_left", mul(num(1), wd("a")), wd("a"),
                                     proven=True)}
    src = eq(mul(vr("x"), num(1)), vr("x"))                       # x·1 = x
    step = {"rule": "mul_one_left", "path": [0], "result": eq(vr("x"), vr("x"))}
    assert sc.check_case(src, [step], rules, ih=None, ac=()).status == "invalid"
    rep = sc.check_case(src, [step], rules, ih=None, ac=("add", "mul"))
    assert rep.status == "certified" and sc.is_reflexive(rep.final, ("add", "mul"))


def test_grade_non_induction_out_of_scope():
    _install(lambda src: True)
    req = {"protocol": "1.0",
           "exercise": {"mode": "transformation", "source": vr("x"), "target": vr("x")},
           "submission": {"final": vr("x")}}
    resp = grade.grade(req)
    assert resp["outcome"] == "unknown" and resp["score"] is None


def test_grade_bad_protocol_raises():
    try:
        grade.grade({"protocol": "2.0", "exercise": ex(eq(powr(num(1), vr("n")), num(1)))})
        assert False
    except grade.RequestError:
        pass


# --- `apply`: n-ary NAMED function application (protocol 1.1) ---------------
# A function is DATA: an `apply` node plus two recursive `definitions` rules (one
# matching `0`, one matching `S k`). Each becomes a Coq `Fixpoint`. Scope: ℕ only.
def ap(f, *args): return {"type": "apply", "value": f, "slots": {"args": list(args)}}


# p and q are the same function under two names, so `p n == q n` is provable by
# induction with the IH used at `n` itself — the shape coqregate can grade.
APPLY_DEFS = [drule("p_zero", ap("p", num(0)), num(1)),
              drule("p_succ", ap("p", succ(wd("k"))), mul(num(2), ap("p", wd("k")))),
              drule("q_zero", ap("q", num(0)), num(1)),
              drule("q_succ", ap("q", succ(wd("k"))), mul(num(2), ap("q", wd("k"))))]
APPLY_GOAL = eq(ap("p", vr("n")), ap("q", vr("n")))


def _apply_ex():
    return {"mode": "induction", "goal": APPLY_GOAL, "inductionVar": "n",
            "definitions": APPLY_DEFS}


def test_apply_emits_a_fixpoint_per_function():
    src = coq_induction.build_source(_apply_ex())
    assert "Fixpoint p (n : nat) {struct n} : Q :=" in src
    assert "Fixpoint q (n : nat) {struct n} : Q :=" in src
    assert "| S k => (2 * (p (k)%nat))" in src
    assert "Theorem regate_induction : forall (n : nat), (p (n)%nat) == (q (n)%nat)." in src


def test_apply_recursion_argument_may_be_any_position():
    # `geo(S k, a)` recurses on its FIRST argument — the constructor-matched one,
    # not "the last" (the cvc5regate contract).
    defs = [drule("geo_zero", ap("geo", num(0), wd("a")), num(1)),
            drule("geo_succ", ap("geo", succ(wd("k")), wd("a")),
                  mul(wd("a"), ap("geo", wd("k"), wd("a"))))]
    src = coq_induction.build_source(
        {"mode": "induction", "goal": eq(ap("geo", vr("n"), vr("c")), ap("geo", vr("n"), vr("c"))),
         "inductionVar": "n", "definitions": defs})
    assert "Fixpoint geo (n : nat) (a : Q) {struct n} : Q :=" in src
    assert "| S k => (a * (geo (k)%nat a))" in src


def test_apply_base_rule_is_renamed_onto_the_step_rule_binders():
    # A Coq Fixpoint has ONE parameter name per position across both branches.
    defs = [drule("f0", ap("f", wd("y"), num(0)), wd("y")),
            drule("fs", ap("f", wd("x"), succ(wd("m"))), mul(wd("x"), ap("f", wd("x"), wd("m"))))]
    src = coq_induction.build_source(
        {"mode": "induction", "goal": eq(ap("f", vr("c"), vr("n")), ap("f", vr("c"), vr("n"))),
         "inductionVar": "n", "definitions": defs})
    assert "Fixpoint f (x : Q) (n : nat) {struct n} : Q :=" in src
    assert "| O => x" in src                      # the base rule's `y` became `x`
    assert "| S m => (x * (f x (m)%nat))" in src


def test_apply_coerces_a_nat_index_used_as_a_value():
    # `fact (S k) = (S k) * fact k` uses its own ℕ index as a ℚ value: ℕ is not ℚ,
    # so the emitted file declares a coercion and applies it.
    defs = [drule("fact_zero", ap("fact", num(0)), num(1)),
            drule("fact_succ", ap("fact", succ(wd("k"))),
                  mul(succ(wd("k")), ap("fact", wd("k"))))]
    src = coq_induction.build_source(
        {"mode": "induction", "goal": eq(ap("fact", vr("n")), ap("fact", vr("n"))),
         "inductionVar": "n", "definitions": defs})
    assert "Fixpoint nq (n : nat) : Q :=" in src
    assert "| S k => ((nq ((S k))%nat) * (fact (k)%nat))" in src


def test_apply_declines_non_structural_recursion():
    # Coq's termination checker would reject the Fixpoint and take the whole file
    # with it; decline with a reason instead (-> unknown, never a grade).
    defs = [drule("g0", ap("g", num(0)), num(1)),
            drule("gs", ap("g", succ(wd("k"))), ap("g", succ(wd("k"))))]
    try:
        coq_induction.build_source(
            {"mode": "induction", "goal": eq(ap("g", vr("n")), ap("g", vr("n"))),
             "inductionVar": "n", "definitions": defs})
        assert False, "expected InductionError"
    except coq_induction.InductionError as e:
        assert "structural" in str(e)


def test_apply_declines_a_name_that_is_not_an_identifier():
    # Transmitted names are interpolated into Coq source; they must be identifiers.
    evil = "bad. Axiom cheat : False"
    defs = [drule("e0", ap(evil, num(0)), num(1)), drule("es", ap(evil, succ(wd("k"))), num(1))]
    try:
        coq_induction.build_source(
            {"mode": "induction", "goal": eq(ap(evil, vr("n")), num(1)),
             "inductionVar": "n", "definitions": defs})
        assert False, "expected InductionError"
    except coq_induction.InductionError:
        pass


def test_apply_declines_a_non_nat_datatype():
    # `exercise.datatype` (lists/trees) is a cvc5regate capability; coqregate is ℕ.
    nil = ap("nil")
    defs = [drule("len_nil", ap("len", nil), num(0)),
            drule("len_cons", ap("len", ap("cons", wd("h"), wd("t"))),
                  add(num(1), ap("len", wd("t"))))]
    try:
        coq_induction.build_source(
            {"mode": "induction", "goal": eq(ap("len", vr("l")), ap("len", vr("l"))),
             "inductionVar": "l", "definitions": defs})
        assert False, "expected InductionError"
    except coq_induction.InductionError:
        pass


def test_apply_pow_path_is_untouched():
    # The `pow` -> `pw` emitter must not learn any `apply` habits: no coercion, no
    # generalization, no restricted unfolding.
    src = coq_induction.build_source(ex(eq(powr(num(1), vr("n")), num(1))))
    assert "nq" not in src and "revert" not in src and "cbn" not in src
    assert "{struct" not in src


def test_grade_apply_derivation_certified():
    _install(lambda src: True)                     # kernel backstop certifies the goal
    e = _apply_ex()
    base = [{"rule": "p_zero", "path": [0], "result": eq(num(1), ap("q", num(0)))},
            {"rule": "q_zero", "path": [1], "result": eq(num(1), num(1))}]
    step = [{"rule": "p_succ", "path": [0],
             "result": eq(mul(num(2), ap("p", vr("n"))), ap("q", succ(vr("n"))))},
            {"rule": "q_succ", "path": [1],
             "result": eq(mul(num(2), ap("p", vr("n"))), mul(num(2), ap("q", vr("n"))))},
            {"kind": "B", "path": [0, 1], "equation": [ap("p", vr("n")), ap("q", vr("n"))],
             "result": eq(mul(num(2), ap("q", vr("n"))), mul(num(2), ap("q", vr("n"))))}]
    resp = grade.grade({"protocol": "1.1", "exercise": e,
                        "submission": {"base": {"steps": base}, "step": {"steps": step}}})
    assert resp["outcome"] == "proven_equal" and resp["certified"] and resp["score"] == 100
    assert "Fixpoint p" in resp["proof"][0]["source"]


def test_grade_apply_invalid_step_is_still_invalid():
    _install(lambda src: True)
    e = _apply_ex()
    base = [{"rule": "p_zero", "path": [0], "result": eq(num(2), ap("q", num(0)))}]   # 1, not 2
    step = [{"rule": "p_succ", "path": [0],
             "result": eq(mul(num(2), ap("p", vr("n"))), ap("q", succ(vr("n"))))}]
    resp = grade.grade({"protocol": "1.1", "exercise": e,
                        "submission": {"base": {"steps": base}, "step": {"steps": step}}})
    assert resp["outcome"] == "invalid_derivation" and resp["score"] == 0


def test_grade_apply_generalized_ih_is_unknown_not_invalid():
    # `fact_aux x (S k) = fact_aux (x·(S k)) k` needs the IH at a SHIFTED
    # accumulator. The emitted Coq proof generalizes the IH, but this backend's
    # step checker only recognises it at the induction variable — so the honest
    # answer is `unknown`. Grading it `invalid_derivation` is the false negative
    # milestone M1 fixed; it must not come back through the `apply` door.
    _install(lambda src: True)
    defs = [drule("fa0", ap("fa", wd("x"), num(0)), wd("x")),
            drule("fas", ap("fa", wd("x"), succ(wd("k"))),
                  ap("fa", mul(wd("x"), succ(wd("k"))), wd("k"))),
            drule("ft0", ap("ft", num(0)), num(1)),
            drule("fts", ap("ft", succ(wd("k"))), mul(succ(wd("k")), ap("ft", wd("k"))))]
    goal = eq(ap("fa", vr("x"), vr("n")), mul(vr("x"), ap("ft", vr("n"))))
    e = {"mode": "induction", "goal": goal, "inductionVar": "n", "definitions": defs}
    shifted = ap("fa", mul(vr("x"), succ(vr("n"))), vr("n"))
    step = [{"rule": "fas", "path": [0], "result": eq(shifted, mul(vr("x"), ap("ft", succ(vr("n")))))},
            {"kind": "B", "path": [0],
             "equation": [shifted, mul(mul(vr("x"), succ(vr("n"))), ap("ft", vr("n")))],
             "result": eq(mul(mul(vr("x"), succ(vr("n"))), ap("ft", vr("n"))),
                          mul(vr("x"), ap("ft", succ(vr("n")))))}]
    # A COMPLETE base case, so the only thing standing between this submission and a
    # verdict is the shifted IH.
    e["ruleset"] = [{"id": "mul_one_right", "lhs": mul(wd("a"), num(1)), "rhs": wd("a"),
                     "bidirectional": False, "conditions": []}]
    base = [{"rule": "fa0", "path": [0], "result": eq(vr("x"), mul(vr("x"), ap("ft", num(0))))},
            {"rule": "ft0", "path": [1, 1], "result": eq(vr("x"), mul(vr("x"), num(1)))},
            {"rule": "mul_one_right", "path": [1], "result": eq(vr("x"), vr("x"))}]
    resp = grade.grade({"protocol": "1.1", "exercise": e,
                        "submission": {"base": {"steps": base}, "step": {"steps": step}}})
    assert resp["outcome"] == "unknown" and resp["score"] is None and not resp["certified"]
    assert resp["meta"]["induction"]["status"] == "uncertifiable"


def test_grade_apply_untranslatable_is_unknown_not_invalid():
    # A list goal (non-ℕ datatype) with a NON-EMPTY submission: the strict step
    # checker must never run on a goal we cannot translate.
    _install(lambda src: True)
    nil = ap("nil")
    defs = [drule("len_nil", ap("len", nil), num(0)),
            drule("len_cons", ap("len", ap("cons", wd("h"), wd("t"))),
                  add(num(1), ap("len", wd("t"))))]
    e = {"mode": "induction", "goal": eq(ap("len", vr("l")), ap("len", vr("l"))),
         "inductionVar": "l", "definitions": defs}
    junk = [{"rule": "len_nil", "path": [0], "result": eq(num(0), num(0))}]
    resp = grade.grade({"protocol": "1.1", "exercise": e,
                        "submission": {"base": {"steps": junk}, "step": {"steps": junk}}})
    assert resp["outcome"] == "unknown" and resp["score"] is None
    assert resp["meta"]["induction"]["status"] == "untranslatable"


def _run_all():
    fns = [v for k, v in sorted(globals().items()) if k.startswith("test_") and callable(v)]
    for fn in fns:
        fn()
        print(f"  ok  {fn.__name__}")
    print(f"\n{len(fns)} passed")


if __name__ == "__main__":
    _run_all()
