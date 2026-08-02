from __future__ import annotations

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import check_induction
import grade
import lean_check
import lean_induction
import lean_prover

# ---- MathNode builders (the protocol JSON shape) ---------------------------
def num(v): return {"type": "number", "value": str(v)}
def vr(v): return {"type": "variable", "value": v}
def wd(v): return {"type": "wild", "value": v}
def bin_(t, l, r): return {"type": t, "slots": {"left": [l], "right": [r]}}
def mul(l, r): return bin_("mul", l, r)
def add(l, r): return bin_("add", l, r)
def eq(l, r): return bin_("eq", l, r)
def succ(x): return {"type": "succ", "slots": {"inner": [x]}}
def ap(name, *args): return {"type": "apply", "value": name, "slots": {"args": list(args)}}
def rule(rid, lhs, rhs, **kw):
    return {"id": rid, "lhs": lhs, "rhs": rhs, "bidirectional": kw.get("bidir", False),
            "conditions": kw.get("conditions", [])}


# `fact_aux x n = x * fact n` — the canonical accumulator/`apply` exercise, defined
# entirely as DATA: two `definitions` rules per function, recursing on `succ`.
FACT_DEFS = [
    rule("factaux_zero", ap("fact_aux", wd("x"), num(0)), wd("x")),
    rule("factaux_succ", ap("fact_aux", wd("x"), succ(wd("k"))),
         ap("fact_aux", mul(wd("x"), succ(wd("k"))), wd("k"))),
    rule("fact_zero", ap("fact", num(0)), num(1)),
    rule("fact_succ", ap("fact", succ(wd("k"))), mul(succ(wd("k")), ap("fact", wd("k")))),
]
FACT_GOAL = eq(ap("fact_aux", vr("x"), vr("n")), mul(vr("x"), ap("fact", vr("n"))))
FACT_EX = {"mode": "induction", "goal": FACT_GOAL, "inductionVar": "n", "definitions": FACT_DEFS}


def _err(fn, *a, **kw) -> str:
    try:
        fn(*a, **kw)
    except lean_induction.InductionError as e:
        return str(e)
    raise AssertionError("expected an InductionError")


# ---------------------------------------------------------------------------
# 1. The `pow` path is untouched.
# ---------------------------------------------------------------------------
def test_pow_source_is_unchanged():
    """The pre-`apply` emitter's output, pinned verbatim. `apply` support must not
    move a single byte of the `pow` → `pw` path."""
    src = lean_induction.build_source(check_induction.MUST_PASS[0][1])
    assert src == (
        "import Mathlib.Data.Rat.Defs\n"
        "import Mathlib.Tactic\n\n"
        "def pw : ℚ → ℕ → ℚ\n"
        "  | a, 0 => (1 : ℚ)\n"
        "  | a, (n + 1) => (a * (pw a n))\n"
        "\n"
        "theorem regate_induction :∀ (n : ℕ), (pw (1 : ℚ) n) = (1 : ℚ) := by\n"
        "  intro n\n"
        "  induction n with\n"
        "  | zero => first | simp_all [pw] | (simp [pw]; ring) | ring\n"
        "  | succ k ih => simp only [pw, Nat.add_eq]; all_goals (first | (rw [ih]; ring)"
        " | (rw [← ih]; ring) | (simp only [ih]; ring) | (simp only [← ih]; ring)"
        " | simp_all [pw, ih])\n"), src
    for _name, ex in check_induction.MUST_PASS:
        s = lean_induction.build_source(ex)
        assert "rg_" not in s and "generalizing" not in s and "push_cast" not in s


def test_pow_without_definitions_still_declines():
    ex = {"mode": "induction", "goal": check_induction.MUST_PASS[0][1]["goal"],
          "inductionVar": "n", "definitions": []}
    assert "pow needs a base rule" in _err(lean_induction.build_source, ex)


# ---------------------------------------------------------------------------
# 2. `apply` translation.
# ---------------------------------------------------------------------------
def test_apply_emits_recursive_defs():
    src = lean_induction.build_source(FACT_EX)
    # A callee is defined before its caller; both are structurally recursive.
    assert src.index("def rg_fact :") < src.index("def rg_fact_aux :")
    assert "def rg_fact : ℕ → ℚ\n  | 0 => (1 : ℚ)\n" in src
    assert "  | (k + 1) => (((k : ℚ) + 1) * (rg_fact k))\n" in src
    assert "def rg_fact_aux : ℚ → ℕ → ℚ\n  | x, 0 => x\n" in src
    assert "  | x, (k + 1) => (rg_fact_aux (x * ((k : ℚ) + 1)) k)\n" in src
    # The accumulator must stay universal in the IH.
    assert "induction n generalizing x with" in src
    assert "(rg_fact_aux x n) = (x * (rg_fact n))" in src
    assert "sorry" not in src and "native_decide" not in src


def test_recursion_argument_may_be_any_position():
    """The constructor-matched argument drives the recursion wherever it sits."""
    defs = [rule("g_zero", ap("g", num(0), wd("x")), wd("x")),
            rule("g_succ", ap("g", succ(wd("k")), wd("x")),
                 ap("g", wd("k"), mul(wd("x"), wd("x"))))]
    ex = {"mode": "induction", "inductionVar": "n", "definitions": defs,
          "goal": eq(ap("g", vr("n"), vr("x")), ap("g", vr("n"), vr("x")))}
    src = lean_induction.build_source(ex)
    assert "def rg_g : ℕ → ℚ → ℚ\n" in src
    assert "  | 0, x => x\n" in src
    assert "  | (k + 1), x => (rg_g k (x * x))\n" in src


def test_nat_variable_in_a_rational_position_is_cast():
    defs = [rule("s_zero", ap("s", num(0)), num(0)),
            rule("s_succ", ap("s", succ(wd("k"))), add(succ(wd("k")), ap("s", wd("k"))))]
    ex = {"mode": "induction", "inductionVar": "n", "definitions": defs,
          "goal": eq(mul(num(2), ap("s", vr("n"))), mul(vr("n"), add(vr("n"), num(1))))}
    src = lean_induction.build_source(ex)
    assert "((2 : ℚ) * (rg_s n)) = ((n : ℚ) * ((n : ℚ) + (1 : ℚ)))" in src
    assert "  | (k + 1) => (((k : ℚ) + 1) + (rg_s k))\n" in src


# ---------------------------------------------------------------------------
# 3. Everything untranslatable declines cleanly (InductionError, never a grade).
# ---------------------------------------------------------------------------
def test_declines_unknown_function():
    ex = dict(FACT_EX, definitions=FACT_DEFS[:2])          # `fact` has no definition
    assert "no recursive definition for function 'fact'" in _err(lean_induction.build_source, ex)


def test_declines_missing_base_or_step_rule():
    ex = dict(FACT_EX, definitions=[FACT_DEFS[0], FACT_DEFS[2], FACT_DEFS[3]])
    assert "exactly one step rule" in _err(lean_induction.build_source, ex)
    ex = dict(FACT_EX, definitions=[FACT_DEFS[1], FACT_DEFS[2], FACT_DEFS[3]])
    assert "exactly two definitions" in _err(lean_induction.build_source, ex)


def test_declines_mutual_recursion():
    defs = [rule("f_zero", ap("f", num(0)), num(0)),
            rule("f_succ", ap("f", succ(wd("k"))), ap("h", wd("k"))),
            rule("h_zero", ap("h", num(0)), num(0)),
            rule("h_succ", ap("h", succ(wd("k"))), ap("f", wd("k")))]
    ex = {"mode": "induction", "inductionVar": "n", "definitions": defs,
          "goal": eq(ap("f", vr("n")), ap("h", vr("n")))}
    assert "mutually recursive" in _err(lean_induction.build_source, ex)


def test_declines_apply_in_a_nat_position():
    defs = [rule("s_zero", ap("s", num(0)), num(0)),
            rule("s_succ", ap("s", succ(wd("k"))), add(succ(wd("k")), ap("s", wd("k"))))]
    ex = {"mode": "induction", "inductionVar": "n", "definitions": defs,
          "goal": eq({"type": "pow", "slots": {"base": [vr("a")],
                                               "exponent": [ap("s", vr("n"))]}}, num(1))}
    assert "cannot appear in a ℕ position" in _err(lean_induction.build_source, ex)


def test_declines_datatype_induction():
    ex = dict(FACT_EX, datatype={"name": "List", "constructors": []})
    assert "datatype induction" in _err(lean_induction.build_source, ex)
    assert "datatype induction" in _err(lean_induction.check_translatable, ex)


def test_declines_truncating_nat_subtraction():
    ex = {"mode": "induction", "inductionVar": "n", "definitions": check_induction.DEFS,
          "goal": eq({"type": "pow", "slots": {
              "base": [vr("a")],
              "exponent": [bin_("sub", vr("n"), vr("m"))]}}, num(1))}
    assert "truncating" in _err(lean_induction.build_source, ex)


def test_declines_names_that_are_not_identifiers():
    """Regate emits source the kernel must check itself, so a caller-supplied name
    never reaches the file unchecked: `sorry` elaborates with exit code 0, and a
    name that closes the term could smuggle one in."""
    evil = "f := by sorry\ntheorem evil : False"
    defs = [rule("e_zero", ap(evil, num(0)), num(0)),
            rule("e_succ", ap(evil, succ(wd("k"))), ap(evil, wd("k")))]
    ex = {"mode": "induction", "inductionVar": "n", "definitions": defs,
          "goal": eq(ap(evil, vr("n")), num(0))}
    assert "not a usable Lean identifier" in _err(lean_induction.build_source, ex)
    bad_var = {"mode": "induction", "inductionVar": "n", "definitions": check_induction.DEFS,
               "goal": eq({"type": "pow", "slots": {"base": [vr("a) := by sorry\ntheorem e")],
                                                    "exponent": [vr("n")]}}, num(1))}
    assert "not a usable Lean identifier" in _err(lean_induction.build_source, bad_var)


# ---------------------------------------------------------------------------
# 4. The step checker: the generalized (accumulator-universal) IH.
# ---------------------------------------------------------------------------
MUL_ASSOC = rule("mul_assoc", mul(mul(wd("a"), wd("b")), wd("c")),
                 mul(wd("a"), mul(wd("b"), wd("c"))))
MUL_ONE = rule("mul_one_right", mul(wd("a"), num(1)), wd("a"))


def _fact_submission():
    """The full fact_aux derivation: base reduces to `x = x`, the step unfolds,
    applies the IH at the SHIFTED accumulator `x*(n+1)`, then reassociates."""
    x, n = vr("x"), vr("n")
    sn = succ(n)
    base = [{"rule": "factaux_zero", "path": [0]},
            {"rule": "fact_zero", "path": [1, 1]},
            {"rule": "mul_one_right", "path": [1]}]
    step = [
        {"rule": "factaux_succ", "path": [0]},
        {"kind": "B", "path": [0],
         "equation": [ap("fact_aux", mul(x, sn), n), mul(mul(x, sn), ap("fact", n))]},
        {"rule": "fact_succ", "path": [1, 1]},
        {"rule": "mul_assoc", "path": [0]},
    ]
    return {"base": {"steps": base}, "step": {"steps": step}}


def _proven(rules):
    return {r["id"]: lean_check.proven_from_custom(r, r["id"]) for r in rules}


def test_generalized_ih_is_accepted():
    ex = dict(FACT_EX, ruleset=[MUL_ASSOC, MUL_ONE])
    rep = lean_check.check_induction(ex, _fact_submission(), _proven([MUL_ASSOC, MUL_ONE]))
    assert rep.status == "certified", (rep.status, rep.reason)


def test_ih_at_a_wrong_instance_is_still_invalid():
    """The IH is universal in `x`, NOT in the induction variable: applying it at
    `n+1` is circular and must stay invalid (conformance fixture 20)."""
    sub = _fact_submission()
    bad = dict(sub["step"]["steps"][1])
    bad["equation"] = [ap("fact_aux", vr("x"), succ(vr("n"))),
                       mul(vr("x"), ap("fact", succ(vr("n"))))]
    sub["step"]["steps"][1] = bad
    ex = dict(FACT_EX, ruleset=[MUL_ASSOC, MUL_ONE])
    rep = lean_check.check_induction(ex, sub, _proven([MUL_ASSOC, MUL_ONE]))
    assert rep.status == "invalid", (rep.status, rep.reason)


def test_apply_rule_instance_keeps_the_function_name():
    """`instantiate` must carry an internal node's `value` — an `apply` template that
    lost its function name matched nothing and failed a correct step."""
    env = {"x": vr("x"), "k": vr("n")}
    out = lean_check.instantiate(FACT_DEFS[1]["rhs"], env)
    assert out["value"] == "fact_aux"
    assert out["slots"]["args"][0]["type"] == "mul"
    assert out["slots"]["args"][1] == vr("n")


# ---------------------------------------------------------------------------
# 5. End to end through grade(), with the kernel stubbed.
# ---------------------------------------------------------------------------
class _FakeLean:
    def __init__(self, accept=lambda body: True):
        self.accept, self.bodies = accept, []

    def __call__(self, body):
        self.bodies.append(body)
        return (True, "") if self.accept(body) else (False, "unsolved goals")


def _install(accept=lambda body: True):
    lean_prover._CACHE.clear()
    lean_induction._CACHE.clear()
    lean_prover.lean_available = lambda: True          # type: ignore[assignment]
    fake = _FakeLean(accept)
    lean_prover._run_lean = fake                       # type: ignore[assignment]
    return fake


def test_grade_certifies_an_apply_induction():
    _install()
    req = {"protocol": "1.1",
           "exercise": dict(FACT_EX, id="fact-aux", ruleset=[MUL_ASSOC, MUL_ONE]),
           "submission": _fact_submission()}
    resp = grade.grade(req)
    assert resp["outcome"] == "proven_equal" and resp["score"] == 100
    assert resp["certified"] is True and resp["proof"]
    assert "def rg_fact_aux" in resp["proof"][0]["source"]


def test_grade_declines_when_the_kernel_rejects_the_goal():
    _install(accept=lambda body: "regate_induction" not in body)   # rules ok, goal not
    req = {"protocol": "1.1",
           "exercise": dict(FACT_EX, id="fact-aux", ruleset=[MUL_ASSOC, MUL_ONE]),
           "submission": _fact_submission()}
    resp = grade.grade(req)
    assert resp["outcome"] == "unknown" and resp["score"] is None
    assert resp["certified"] is False


def test_untranslatable_vocabulary_grades_unknown_not_invalid():
    """A submission Leanregate cannot translate must decline, never be scored 0 —
    the M1/M2 false-negative class."""
    _install()
    ex = dict(FACT_EX, id="lists", datatype={"name": "List", "constructors": []},
              ruleset=[MUL_ASSOC, MUL_ONE])
    resp = grade.grade({"protocol": "1.1", "exercise": ex, "submission": _fact_submission()})
    assert resp["outcome"] == "unknown" and resp["score"] is None
    assert resp["meta"]["induction"]["submission"] == "untranslatable"


def test_a_wrong_apply_step_is_still_invalid():
    _install()
    sub = _fact_submission()
    sub["base"]["steps"][0] = {"rule": "factaux_zero", "path": [0],
                               "result": eq(vr("x"), num(7))}    # fabricated result
    req = {"protocol": "1.1",
           "exercise": dict(FACT_EX, id="fact-aux", ruleset=[MUL_ASSOC, MUL_ONE]),
           "submission": sub}
    resp = grade.grade(req)
    assert resp["outcome"] == "invalid_derivation" and resp["score"] == 0


def _run_all():
    fns = [v for k, v in sorted(globals().items()) if k.startswith("test_") and callable(v)]
    for fn in fns:
        fn()
        print(f"  ok  {fn.__name__}")
    print(f"\n{len(fns)} passed")


if __name__ == "__main__":
    _run_all()
