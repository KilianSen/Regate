from __future__ import annotations

import copy
import hashlib
from dataclasses import dataclass

import coq_prover  # reuse the kernel seam: check_source, coq_available, caching
import step_check  # strict symbolic rule-instance checking of the student's steps

FUN = "pw"           # the Coq name for the model's `pow` node
THEOREM = "regate_induction"


class InductionError(ValueError):
    """The induction goal/definitions are outside the supported Coq fragment."""


# ---------------------------------------------------------------------------
# Typing: which variables are ℕ (exponents / the induction var) vs ℚ.
# Mirrors lean_induction._infer one-for-one (the model is backend-agnostic).
# ---------------------------------------------------------------------------
def _infer(node: dict, dom: str, env: dict[str, str]) -> None:
    t = node.get("type")
    if t in ("variable", "wild"):
        name = str(node["value"])
        if env.get(name, dom) != dom:
            raise InductionError(f"variable {name!r} is used as both ℚ and ℕ")
        env[name] = dom
        return
    if t == "number":
        return
    s = node.get("slots") or {}
    if t == "succ":
        _infer(s["inner"][0], "N", env)
    elif t == "pow":
        _infer(s["base"][0], "Q", env)
        _infer(s["exponent"][0], "N", env)
    elif t == "frac":
        _infer(s["numerator"][0], "Q", env)
        _infer(s["denominator"][0], "Q", env)
    elif t in ("add", "sub", "mul"):
        _infer(s["left"][0], dom, env)
        _infer(s["right"][0], dom, env)
    elif t == "neg":
        _infer(s["inner"][0], dom, env)
    elif t == "eq":
        _infer(s["left"][0], "Q", env)
        _infer(s["right"][0], "Q", env)
    else:
        raise InductionError(f"cannot type node type {t!r}")


# ---------------------------------------------------------------------------
# MathNode -> Coq term, domain-aware (ℚ or ℕ).
#
# The file opens `Q_scope`, so ℚ operators/numerals are the default. ℕ
# subterms (exponents) must be forced into `nat` scope, so every `pow`
# application wraps its exponent in `(...)%nat` — inside which `+ - * S` and
# numerals parse as ℕ.
# ---------------------------------------------------------------------------
_BIN = {"add": "+", "sub": "-", "mul": "*"}


def _term(node: dict, dom: str) -> str:
    t = node.get("type")
    if t in ("variable", "wild"):
        return str(node["value"])
    if t == "number":
        # In Q_scope a bare numeral is a ℚ literal; ℕ numerals sit inside a
        # `(...)%nat` region (the pow exponent) so a bare numeral is fine there.
        return str(node["value"])
    s = node["slots"]
    if t == "succ":
        return f"(S {_term(s['inner'][0], 'N')})"
    if t == "pow":
        # base is ℚ; the exponent is ℕ — force nat scope around it.
        return f"({FUN} {_term(s['base'][0], 'Q')} ({_term(s['exponent'][0], 'N')})%nat)"
    if t in _BIN:
        return f"({_term(s['left'][0], dom)} {_BIN[t]} {_term(s['right'][0], dom)})"
    if t == "frac":
        return f"({_term(s['numerator'][0], 'Q')} / {_term(s['denominator'][0], 'Q')})"
    if t == "neg":
        return f"(- {_term(s['inner'][0], dom)})"
    raise InductionError(f"cannot translate node type {t!r}")


# ---------------------------------------------------------------------------
# The recursive `pw` definition, derived from the transmitted definitions.
# ---------------------------------------------------------------------------
def _wild_name(node: dict) -> str:
    if node.get("type") not in ("wild", "variable"):
        raise InductionError("expected a wildcard in the definition pattern")
    return str(node["value"])


def _rename(node: dict, mapping: dict[str, str]) -> dict:
    """Copy `node`, remapping wildcard/variable names per `mapping`.

    A Coq `Fixpoint` has fixed parameter names across both match branches, but
    the transmitted base/succ rules may use different wildcard names. We rename
    each rule's body to the canonical Fixpoint binders before translating."""
    out = copy.deepcopy(node)

    def go(n: dict) -> None:
        if n.get("type") in ("wild", "variable"):
            nm = str(n.get("value"))
            if nm in mapping:
                n["value"] = mapping[nm]
            return
        for children in (n.get("slots") or {}).values():
            for ch in children:
                go(ch)

    go(out)
    return out


def _build_pow_def(definitions: list[dict]) -> str:
    """`Fixpoint pw (a:Q)(n:nat) : Q` from `pow(a,0)→…` and `pow(a,S n)→…`.

    Canonical binders: first param `a` (ℚ base), match binder `k` (ℕ predecessor)."""
    base_rule = succ_rule = None
    for d in definitions:
        lhs = d.get("lhs", {})
        if lhs.get("type") != "pow":
            continue
        exp = lhs["slots"]["exponent"][0]
        if exp.get("type") == "number" and str(exp.get("value")) == "0":
            base_rule = d
        elif exp.get("type") == "succ":
            succ_rule = d
    if base_rule is None or succ_rule is None:
        raise InductionError(
            "pow needs a base rule (pow(a,0)→…) and a successor rule (pow(a,S n)→…)")

    b_var = _wild_name(base_rule["lhs"]["slots"]["base"][0])
    base_body = _term(_rename(base_rule["rhs"], {b_var: "a"}), "Q")

    s_var = _wild_name(succ_rule["lhs"]["slots"]["base"][0])
    rec_var = _wild_name(succ_rule["lhs"]["slots"]["exponent"][0]["slots"]["inner"][0])
    succ_body = _term(_rename(succ_rule["rhs"], {s_var: "a", rec_var: "k"}), "Q")
    return (
        f"Fixpoint {FUN} (a : Q) (n : nat) : Q :=\n"
        f"  match n with\n"
        f"  | O => {base_body}\n"
        f"  | S k => {succ_body}\n"
        f"  end.\n"
    )


# ---------------------------------------------------------------------------
# The whole Coq file: imports + definition + theorem + induction proof.
# ---------------------------------------------------------------------------
def build_source(ex: dict) -> str:
    goal = ex.get("goal")
    if not goal or goal.get("type") != "eq":
        raise InductionError("induction goal must be an equality")
    var = ex.get("inductionVar")
    if not var:
        raise InductionError("missing inductionVar")

    env: dict[str, str] = {}
    _infer(goal, "Q", env)
    if env.get(var) != "N":
        raise InductionError(f"induction variable {var!r} must be a ℕ (exponent) variable")

    q_vars = sorted(v for v, d in env.items() if d == "Q")
    n_vars = sorted(v for v, d in env.items() if d == "N")
    fresh = next(c for c in ("k", "m", "p", "q", "i", "j") if c not in env)
    ihn = "ih" if "ih" not in env else "ih0"

    pow_def = _build_pow_def(ex.get("definitions") or [])
    lhs = _term(goal["slots"]["left"][0], "Q")
    rhs = _term(goal["slots"]["right"][0], "Q")

    binder_groups = []
    if q_vars:
        binder_groups.append(f"({' '.join(q_vars)} : Q)")
    binder_groups.append(f"({' '.join(n_vars)} : nat)")
    binders = " ".join(binder_groups)
    intro = " ".join(q_vars + n_vars)

    # We prove the goal as a `Qeq` (`==`), the setoid equality `ring`/`field`
    # discharge over ℚ — see the module docstring for why not Leibniz `=`.
    #
    # Both obligations: first normalise nat arithmetic the `induction` left in the
    # exponent — `n + 0 → n` (Nat.add_0_r) for the base, `m + S k → S (m + k)`
    # (Nat.add_succ_r) for the step — so `simpl` can unfold `pw` at `O`/`S _`.
    # `repeat rewrite` is a no-op when the lemma does not apply, so the same line
    # serves goals with and without `+` in the exponent. Then close, cheapest
    # first: bare `ring`; forward IH rewrite (`1^n`, `aᵐ⁺ⁿ`); backward IH fold
    # (`aⁿ·bⁿ=(a·b)ⁿ`, folding the product under one `pow`). `first` takes
    # whichever closes; the backward fold is reached only after the forward
    # rewrite fails, so it never loops on an IH with a literal RHS. All branches
    # are sound — Coq's kernel re-checks the chosen one. (Verified on Rocq 9.1.1.)
    norm = "repeat rewrite Nat.add_succ_r; repeat rewrite Nat.add_0_r; simpl"
    return (
        # `From Coq Require` works on both Coq 8.x and Rocq 9.x (deprecated-with-
        # warning on 9.x, which coq_prover silences). Stdlib only — no Mathlib.
        "From Coq Require Import QArith.\n"
        "From Coq Require Import Arith.\n"
        "From Coq Require Import Lia.\n"
        "Open Scope Q_scope.\n\n"
        f"{pow_def}\n"
        f"Theorem {THEOREM} : forall {binders}, {lhs} == {rhs}.\n"
        f"Proof.\n"
        f"  intros {intro}.\n"
        f"  induction {var} as [| {fresh} {ihn}].\n"
        f"  - {norm}; first [ ring | rewrite {ihn}; ring | rewrite <- {ihn}; ring ].\n"
        f"  - {norm}; first [ ring | rewrite {ihn}; ring | rewrite <- {ihn}; ring "
        f"| (field; lia) ].\n"
        f"Qed.\n"
    )


# ---------------------------------------------------------------------------
# The ruleset's trust boundary.
#
# Regate's premise: a ruleset is authored and formally validated ONCE, upstream.
# This backend validates the student's *derivation* against it, so by default it
# takes the caller's warrant and does not re-prove 29 rules on every submission
# (~0.35 s of coqc each, and the CLI transport runs cold in a per-submission
# container).
#
# That warrant is only worth what enforces it, so it can be checked here:
#
#   * `options.verify_rules` re-establishes it from scratch — each rule gets its
#     own Coq kernel run. Use it for rules from an untrusted source (a hand-authoring
#     UI) or in CI.
#   * a rule carrying a `proof` (a Coq tactic script) is *checked* rather than
#     searched for — the proof-carrying path, cheap, and how an authoring pipeline
#     should ship its evidence. Mirrors leanregate's `_carried_source`.
#
# Why this matters at all: a step that correctly applies a *false* rule proves
# nothing, and the induction backstop certifies the goal, not the ruleset — so
# `1^n = 1` certifies even when the student's step cited `a*b = b`. A rule Coq
# cannot prove (or a guarded one, whose side condition we do not model) is simply
# not proven: a step citing it grades `unknown`, never `invalid` — the student
# followed the rule they were handed. Recursive `definitions` are definitional,
# hence always trusted.
# ---------------------------------------------------------------------------
RULE_THEOREM = "regate_rule"


@dataclass
class ProvenRule:
    id: str
    proven: bool
    # "trusted"  -- taken on the caller's warrant (verify_rules off)
    # "carried"  -- the rule shipped a Coq proof and the kernel accepted it
    # "ring"     -- the kernel proved it from scratch
    method: str      # …| "rejected" | "guarded" | "unavailable" | "untranslatable"
    detail: str = ""


def verify_rules_enabled(ex: dict) -> bool:
    """Should the transmitted ruleset be re-verified rather than trusted?"""
    return bool((ex.get("options") or {}).get("verify_rules"))


def build_rule_source(rule: dict, definitions: list[dict] | None = None,
                      tactic: str | None = None) -> str:
    """A standalone Coq file proving `forall vars, lhs == rhs` for one rule.

    ``tactic`` overrides the automatic tactic with the rule's carried proof script.
    """
    lhs_node, rhs_node = rule.get("lhs"), rule.get("rhs")
    if not lhs_node or not rhs_node:
        raise InductionError("rule needs lhs and rhs")

    env: dict[str, str] = {}
    _infer(lhs_node, "Q", env)
    _infer(rhs_node, "Q", env)

    lhs, rhs = _term(lhs_node, "Q"), _term(rhs_node, "Q")
    q_vars = sorted(v for v, d in env.items() if d == "Q")
    n_vars = sorted(v for v, d in env.items() if d == "N")

    binder_groups = []
    if q_vars:
        binder_groups.append(f"({' '.join(q_vars)} : Q)")
    if n_vars:
        binder_groups.append(f"({' '.join(n_vars)} : nat)")
    binders = " ".join(binder_groups)
    intro = " ".join(q_vars + n_vars)

    # `pw` is only needed when the rule mentions `pow`; a rule that does not is
    # provable without the definitions (and must be, since they may be absent).
    pow_def = ""
    if _mentions_pow(lhs_node) or _mentions_pow(rhs_node):
        pow_def = _build_pow_def(definitions or []) + "\n"

    forall = f"forall {binders}, " if binders else ""
    auto = "first [ ring | simpl; ring | field | (field; lia) | (simpl; field) ]"
    body = tactic if tactic is not None else auto
    return (
        "From Coq Require Import QArith.\n"
        "From Coq Require Import Arith.\n"
        "From Coq Require Import Lia.\n"
        "Open Scope Q_scope.\n\n"
        f"{pow_def}"
        f"Theorem {RULE_THEOREM} : {forall}{lhs} == {rhs}.\n"
        f"Proof.\n"
        f"  {'intros ' + intro + ';' if intro else ''} {body}.\n"
        f"Qed.\n"
    )


def _mentions_pow(node: dict) -> bool:
    if node.get("type") == "pow":
        return True
    return any(_mentions_pow(ch)
               for children in (node.get("slots") or {}).values() for ch in children)


_RULE_CACHE: dict[str, ProvenRule] = {}


def prove_rule(rule: dict, definitions: list[dict] | None = None) -> ProvenRule:
    """Kernel-prove one transmitted rule. Unproven is inconclusive, not false.

    Prefers the rule's *carried* proof when it has one (checking a supplied script
    is cheaper than searching for a tactic that works); falls back to the automatic
    tactic. Only called when `options.verify_rules` is set.
    """
    rid = str(rule.get("id", "?"))
    if rule.get("conditions"):
        # A guarded rule (`x/x = 1` needing `x != 0`) is not an unconditional
        # equality; we do not model the side condition, so we cannot prove it.
        # (step_check refuses guarded rules independently, trusted or not.)
        return ProvenRule(rid, False, "guarded",
                          "guarded rules are outside the certifiable fragment")

    carried = rule.get("proof")
    try:
        source = build_rule_source(rule, definitions, tactic=carried or None)
    except InductionError as e:
        return ProvenRule(rid, False, "untranslatable", str(e))

    key = hashlib.sha256(source.encode()).hexdigest()
    if key in _RULE_CACHE:
        return _RULE_CACHE[key]
    if not coq_prover.coq_available():
        return ProvenRule(rid, False, "unavailable", "coq toolchain unavailable")

    ok, detail = coq_prover.check_source(source)
    if ok:
        result = ProvenRule(rid, True, "carried" if carried else "ring")
    elif carried:
        # The author's own script did not check. Try to prove it anyway before
        # calling the rule unproven — a stale proof should not fail a sound rule.
        try:
            ok2, detail2 = coq_prover.check_source(build_rule_source(rule, definitions))
        except InductionError as e:
            ok2, detail2 = False, str(e)
        result = (ProvenRule(rid, True, "ring", "carried proof rejected; auto-proved instead")
                  if ok2 else ProvenRule(rid, False, "rejected", detail2[:400]))
    else:
        result = ProvenRule(rid, False, "rejected", detail[:400])
    _RULE_CACHE[key] = result
    return result


def prove_ruleset(ex: dict) -> dict[str, ProvenRule]:
    """Establish the ruleset's soundness, keyed by rule id.

    By default this is the caller's warrant, not a kernel run: Regate's premise is
    that a ruleset is authored and formally validated upstream, and this backend
    grades derivations against it. `options.verify_rules` re-establishes it here.
    """
    rules = ex.get("ruleset") or []
    if not verify_rules_enabled(ex):
        return {str(r.get("id")): ProvenRule(
            str(r.get("id")), True, "trusted",
            "ruleset warranted valid by the caller; set options.verify_rules to re-prove")
            for r in rules}
    defs = ex.get("definitions") or []
    return {str(r.get("id")): prove_rule(r, defs) for r in rules}


# ---------------------------------------------------------------------------
# Public API.
# ---------------------------------------------------------------------------
@dataclass
class CertifyResult:
    certified: bool
    method: str      # "induction" | "rejected" | "unavailable" | "untranslatable"
    detail: str = ""


_CACHE: dict[str, CertifyResult] = {}


def certify(ex: dict) -> CertifyResult:
    """Certify `∀ inductionVar. goal` with a Coq `induction` kernel run."""
    try:
        source = build_source(ex)
    except InductionError as e:
        return CertifyResult(False, "untranslatable", str(e))

    key = hashlib.sha256(source.encode()).hexdigest()
    if key in _CACHE:
        return _CACHE[key]
    if not coq_prover.coq_available():
        return CertifyResult(False, "unavailable", "coq toolchain unavailable")

    ok, detail = coq_prover.check_source(source)
    result = CertifyResult(True, "induction") if ok else CertifyResult(False, "rejected", detail)
    _CACHE[key] = result
    return result


# ---------------------------------------------------------------------------
# Grading the STUDENT's derivation strictly (rule-instance, NOT value-equivalence).
#
# Each step must be an instance of the *claimed rule* at the *claimed path*
# producing exactly the claimed result (step_check); each Type-B step must
# substitute exactly the inductive hypothesis. A step that reaches a value-equal
# state by any other means than the claimed rule is rejected — no leniency. Both
# obligations must reduce to a reflexive `t = t`. The Coq kernel then BACKSTOPS
# the leap: it certifies the goal (guarding against unsound transmitted
# definitions), so a derivation of valid rule-instances that closes both
# obligations certifies ∀n.P(n). Invalid step ⇒ `invalid`; an unknown/guarded
# rule, or a goal the kernel cannot certify ⇒ `uncertifiable` (→ unknown); a
# missing/half-empty submission ⇒ `unattempted` (→ unknown) — never an auto-pass.
# ---------------------------------------------------------------------------
@dataclass
class GradeResult:
    status: str      # "certified" | "invalid" | "unattempted" | "uncertifiable" | "untranslatable" | "unavailable"
    reason: str = ""
    source: str = ""                    # the Coq file the kernel accepted (certificate)
    ruleset: dict | None = None         # per-rule proof status, for meta


def grade_derivation(ex: dict, sub: dict) -> GradeResult:
    goal = ex.get("goal")
    var = ex.get("inductionVar")
    if not goal or goal.get("type") != "eq" or not var:
        return GradeResult("untranslatable", "goal must be an equality with an inductionVar")
    var = str(var)

    # Prove the transmitted ruleset FIRST: a rule Coq cannot prove may never be
    # composed into a certified derivation, however correctly the student applies it.
    proven = prove_ruleset(ex)
    ruleset_meta = {rid: {"proven": p.proven, "method": p.method, "detail": p.detail}
                    for rid, p in proven.items()}

    base_steps = (sub.get("base") or {}).get("steps")
    step_steps = (sub.get("step") or {}).get("steps")
    if not base_steps or not step_steps:
        return GradeResult("unattempted",
                           "no induction derivation submitted (need both a base-case and an "
                           "inductive-step derivation)", ruleset=ruleset_meta)

    rules = step_check.build_rules(ex, {rid for rid, p in proven.items() if p.proven})
    ac = step_check.ac_ops(ex)   # () unless exercise.options.ac_normalization
    # Base: reduce P(0) to a tautology using the claimed rules only.
    base0 = step_check.substitute(goal, var, {"type": "number", "value": "0"})
    base = step_check.check_case(base0, base_steps, rules, ih=None, ac=ac)
    if base.status == "invalid":
        return GradeResult("invalid", f"base case: {base.reason}", ruleset=ruleset_meta)
    if base.status != "certified":
        return GradeResult("uncertifiable", f"base case: {base.reason}", ruleset=ruleset_meta)
    if not step_check.is_reflexive(base.final, ac):
        return GradeResult("invalid", "base case did not reduce both sides to a common form (t = t)",
                           ruleset=ruleset_meta)
    # Step: reduce P(S n) to a tautology, licensed to substitute the IH P(n).
    succ = {"type": "succ", "slots": {"inner": [{"type": "variable", "value": var}]}}
    step0 = step_check.substitute(goal, var, succ)
    ih = (goal["slots"]["left"][0], goal["slots"]["right"][0])
    stp = step_check.check_case(step0, step_steps, rules, ih=ih, ac=ac)
    if stp.status == "invalid":
        return GradeResult("invalid", f"inductive step: {stp.reason}", ruleset=ruleset_meta)
    if stp.status != "certified":
        return GradeResult("uncertifiable", f"inductive step: {stp.reason}", ruleset=ruleset_meta)
    if not step_check.is_reflexive(stp.final, ac):
        return GradeResult("invalid", "inductive step did not reduce both sides to a common form (t = t)",
                           ruleset=ruleset_meta)

    # Every student step is an instance of a rule the kernel PROVED, and both
    # obligations close. The Coq kernel backstops the induction leap (and guards
    # the definitions).
    if not coq_prover.coq_available():
        return GradeResult("uncertifiable",
                           "derivation steps are valid but the Coq kernel is unavailable to "
                           "certify the induction leap", ruleset=ruleset_meta)
    cert = certify(ex)
    if cert.certified:
        try:
            source = build_source(ex)
        except InductionError:            # cannot happen: certify() just built it
            source = ""
        return GradeResult("certified",
                           "every step is an instance of a Coq-proven rule, and the Coq kernel "
                           "certifies the induction",
                           source=source, ruleset=ruleset_meta)
    return GradeResult("uncertifiable",
                       f"derivation steps are valid but the Coq backstop did not certify the goal "
                       f"({cert.method})", ruleset=ruleset_meta)
