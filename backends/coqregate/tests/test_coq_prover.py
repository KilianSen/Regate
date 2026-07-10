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


def test_unsound_rule_is_never_certified():
    # The bug this pins: the Coq kernel certifies the GOAL, not the ruleset. With a
    # true goal (1ⁿ = 1) and a step citing the FALSE rule `a·b = b`, correctly applied,
    # coqregate used to return proven_equal/100/certified. An unproven rule must make
    # the derivation `unknown` — inconclusive, not a wrong answer.
    unsound = [{"id": "drop_left", "lhs": mul(wd("a"), wd("b")), "rhs": wd("b"),
                "bidirectional": False, "conditions": []}]
    step = [dict(s) for s in VALID_STEP]
    step[2] = dict(step[2], rule="drop_left")
    # The kernel accepts the induction goal but rejects the rule's own theorem.
    _install(lambda src: f"Theorem {coq_induction.RULE_THEOREM}" not in src)
    resp = grade.grade(_ind_req(_sub(VALID_BASE, step), ruleset=unsound))
    assert resp["outcome"] == "unknown" and resp["score"] is None and not resp["certified"]
    assert resp["meta"]["ruleset"]["drop_left"]["proven"] is False


def test_proven_rule_is_certified():
    # ...and the same shape with a rule the kernel *does* prove still certifies.
    _install(lambda src: True)
    resp = grade.grade(_ind_req(_sub(VALID_BASE, VALID_STEP)))
    assert resp["outcome"] == "proven_equal" and resp["certified"]
    assert resp["meta"]["ruleset"]["mul_one_left"]["proven"] is True


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


def _run_all():
    fns = [v for k, v in sorted(globals().items()) if k.startswith("test_") and callable(v)]
    for fn in fns:
        fn()
        print(f"  ok  {fn.__name__}")
    print(f"\n{len(fns)} passed")


if __name__ == "__main__":
    _run_all()
