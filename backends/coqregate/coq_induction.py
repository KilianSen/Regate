from __future__ import annotations

import copy
import hashlib
import re
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
#
# `sigs` (since the `apply` support) maps a named function to its per-argument
# domains, derived from the transmitted `definitions` — see `_signatures`. It is
# empty for a request that uses no `apply` node, and then this function behaves
# exactly as it did before: an `apply` node has no domain and is refused.
#
# `indvar`, when given (only on the `apply` path), exempts the induction variable
# from the ℚ/ℕ consistency check: a ℕ index may legitimately appear BOTH as a
# recursion argument (`sum n`) and as a value (`n * (n + 2)`), the latter through
# the emitted ℕ→ℚ coercion. Every other variable still has exactly one domain.
# ---------------------------------------------------------------------------
def _infer(node: dict, dom: str, env: dict[str, str],
           sigs: dict[str, list[str]] | None = None, indvar: str = "") -> None:
    t = node.get("type")
    if t in ("variable", "wild"):
        name = str(node["value"])
        if indvar and name == indvar:
            env[name] = "N"          # ℕ everywhere; coerced where a ℚ is wanted
            return
        if env.get(name, dom) != dom:
            raise InductionError(f"variable {name!r} is used as both ℚ and ℕ")
        env[name] = dom
        return
    if t == "number":
        return
    s = node.get("slots") or {}
    if t == "succ":
        _infer(s["inner"][0], "N", env, sigs, indvar)
    elif t == "pow":
        _infer(s["base"][0], "Q", env, sigs, indvar)
        _infer(s["exponent"][0], "N", env, sigs, indvar)
    elif t == "frac":
        _infer(s["numerator"][0], "Q", env, sigs, indvar)
        _infer(s["denominator"][0], "Q", env, sigs, indvar)
    elif t in ("add", "sub", "mul"):
        _infer(s["left"][0], dom, env, sigs, indvar)
        _infer(s["right"][0], dom, env, sigs, indvar)
    elif t == "neg":
        _infer(s["inner"][0], dom, env, sigs, indvar)
    elif t == "eq":
        _infer(s["left"][0], "Q", env, sigs, indvar)
        _infer(s["right"][0], "Q", env, sigs, indvar)
    elif t == "apply":
        name = str(node.get("value"))
        sig = (sigs or {}).get(name)
        if sig is None:
            raise InductionError(
                f"unknown function {name!r} (no recursive definition transmitted for it)")
        args = s.get("args") or []
        if len(args) != len(sig):
            raise InductionError(
                f"{name!r} is applied to {len(args)} argument(s) but defined with {len(sig)}")
        for a, d in zip(args, sig):
            _infer(a, d, env, sigs, indvar)
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


class _Ctx:
    """Translation state for a request that uses `apply` (named function application).

    `sigs`  — function name → per-argument domain ("N" for the constructor-matched
              recursion argument, "Q" for the rest); see `_signatures`.
    `env`   — variable name → domain, for the region being translated (the goal, or
              one Fixpoint body with its own binders).
    `nq`    — the name of the emitted ℕ→ℚ coercion. A ℚ-valued recursive function
              over ℕ routinely mentions its own index as a value (`fact (S k) =
              (S k) * fact k`), and ℕ is not ℚ, so those spots need a coercion.
              `flags` is shared by every scoped copy so the emitter knows whether to
              declare it at all.

    A request with no `apply` node builds NO context (`ctx is None`) and every
    translation below is byte-for-byte what it was before `apply` existed.
    """

    def __init__(self, sigs: dict[str, list[str]], env: dict[str, str],
                 nq: str = "nq", flags: dict | None = None):
        self.sigs = sigs
        self.env = env
        self.nq = nq
        self.flags = flags if flags is not None else {"nq": False}

    def scoped(self, env: dict[str, str]) -> "_Ctx":
        """Same functions/coercion, different binders (one Fixpoint body)."""
        return _Ctx(self.sigs, env, self.nq, self.flags)

    def coerce(self, nat_term: str) -> str:
        """Place a ℕ term where a ℚ value is required."""
        self.flags["nq"] = True
        return f"({self.nq} ({nat_term})%nat)"

    @property
    def need_nq(self) -> bool:
        return self.flags["nq"]


def _term(node: dict, dom: str, ctx: _Ctx | None = None) -> str:
    t = node.get("type")
    if t in ("variable", "wild"):
        name = str(node["value"])
        if ctx is not None:
            tag = ctx.env.get(name)
            if dom == "Q" and tag == "N":
                return ctx.coerce(name)
            if dom == "N" and tag == "Q":
                raise InductionError(f"variable {name!r} is a ℚ value, not a ℕ")
        return name
    if t == "number":
        # In Q_scope a bare numeral is a ℚ literal; ℕ numerals sit inside a
        # `(...)%nat` region (the pow exponent) so a bare numeral is fine there.
        return str(node["value"])
    s = node["slots"]
    if t == "succ":
        nat = f"(S {_term(s['inner'][0], 'N', ctx)})"
        # `S k` in a ℚ position (a recursive definition using its own index as a
        # value) is coerced; in a ℕ position it stays a ℕ.
        return ctx.coerce(nat) if (ctx is not None and dom == "Q") else nat
    if t == "pow":
        # base is ℚ; the exponent is ℕ — force nat scope around it.
        return f"({FUN} {_term(s['base'][0], 'Q', ctx)} ({_term(s['exponent'][0], 'N', ctx)})%nat)"
    if t in _BIN:
        return f"({_term(s['left'][0], dom, ctx)} {_BIN[t]} {_term(s['right'][0], dom, ctx)})"
    if t == "frac":
        return f"({_term(s['numerator'][0], 'Q', ctx)} / {_term(s['denominator'][0], 'Q', ctx)})"
    if t == "neg":
        return f"(- {_term(s['inner'][0], dom, ctx)})"
    if t == "apply":
        if ctx is None:
            raise InductionError(
                "`apply` needs the recursive definitions that give the function a meaning")
        name = str(node.get("value"))
        sig = ctx.sigs.get(name)
        if sig is None:
            raise InductionError(
                f"unknown function {name!r} (no recursive definition transmitted for it)")
        args = s.get("args") or []
        if len(args) != len(sig):
            raise InductionError(
                f"{name!r} is applied to {len(args)} argument(s) but defined with {len(sig)}")
        if dom != "Q":
            raise InductionError(f"{name!r} returns a ℚ value; it cannot be used as a ℕ")
        # A ℕ argument is forced into nat scope exactly like a `pow` exponent.
        parts = [f"({_term(a, 'N', ctx)})%nat" if d == "N" else _term(a, "Q", ctx)
                 for a, d in zip(args, sig)]
        return f"({name} {' '.join(parts)})" if parts else name
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


def _build_pow_def(definitions: list[dict], ctx: _Ctx | None = None) -> str:
    """`Fixpoint pw (a:Q)(n:nat) : Q` from `pow(a,0)→…` and `pow(a,S n)→…`.

    Canonical binders: first param `a` (ℚ base), match binder `k` (ℕ predecessor)."""
    if ctx is not None:
        # The Fixpoint's own binders, NOT the goal's: `a` is the ℚ base and `k` the
        # ℕ predecessor whatever the goal happens to call its variables.
        ctx = ctx.scoped({"a": "Q", "k": "N"})
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
    base_body = _term(_rename(base_rule["rhs"], {b_var: "a"}), "Q", ctx)

    s_var = _wild_name(succ_rule["lhs"]["slots"]["base"][0])
    rec_var = _wild_name(succ_rule["lhs"]["slots"]["exponent"][0]["slots"]["inner"][0])
    succ_body = _term(_rename(succ_rule["rhs"], {s_var: "a", rec_var: "k"}), "Q", ctx)
    return (
        f"Fixpoint {FUN} (a : Q) (n : nat) : Q :=\n"
        f"  match n with\n"
        f"  | O => {base_body}\n"
        f"  | S k => {succ_body}\n"
        f"  end.\n"
    )


# ---------------------------------------------------------------------------
# `apply` — n-ary NAMED function application (protocol 1.1).
#
# The point of the node: a host adds a new binary/n-ary operator as DATA — an
# `apply` node plus two recursive `definitions` rules — instead of a new MathNode
# type wired into every backend by hand. A function is defined by exactly two
# transmitted rules, one matching the ℕ base constructor `0` and one matching the
# step constructor `S k`, recursing on the constructor-matched argument, which may
# sit at ANY position (`fact_aux(x, S k)` recurses on its second, `sum(S k)` on its
# first). Each becomes one Coq `Fixpoint` with a two-branch `match`.
#
# SCOPE (v1): ℕ only — `O`/`S`, matching coqregate's ℚ-goal / ℕ-exponent typing.
# `exercise.datatype` (lists, trees) is NOT implemented: a definition that matches
# a non-ℕ constructor has no ℕ constructor in any argument and is declined here,
# which surfaces as `unknown`, never a grade.
# ---------------------------------------------------------------------------
_IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_']*\Z")
# Enough of Coq's syntax to keep a transmitted name from becoming a parse error (or
# worse, silently meaning something else) in the emitted file.
_RESERVED = {
    "forall", "fun", "match", "with", "end", "in", "let", "fix", "cofix", "struct",
    "if", "then", "else", "return", "as", "at", "Prop", "Set", "Type", "where",
    "nat", "O", "S", "Q", "Definition", "Fixpoint", "Theorem", "Proof", "Qed",
    FUN, THEOREM,
}


def _ident(name: str, what: str) -> str:
    """A transmitted name is interpolated straight into Coq source — it must be a
    plain identifier, not syntax."""
    if not _IDENT.match(name or "") or name in _RESERVED:
        raise InductionError(f"{what} {name!r} is not a usable Coq identifier")
    return name


def _fresh(base: str, used: set[str]) -> str:
    name, i = base, 0
    while name in used:
        i += 1
        name = f"{base}{i}"
    return name


def _is_nat_ctor(node: dict) -> bool:
    """Is this argument a ℕ constructor pattern — `0` (base) or `S k` (step)?"""
    t = node.get("type")
    return (t == "number" and str(node.get("value")) == "0") or t == "succ"


def _rec_index(args: list) -> int | None:
    """Position of the constructor-matched argument — the one recursed on. Any
    position, not necessarily the last."""
    for i, a in enumerate(args):
        if _is_nat_ctor(a):
            return i
    return None


def _signatures(definitions: list[dict]) -> dict[str, list[str]]:
    """function name → per-argument domain, read off the transmitted definitions.

    An argument is ℕ exactly where some rule matches a ℕ constructor on it; every
    other argument is a ℚ value. Empty when the request uses no `apply` — which is
    the switch that keeps the `pow`/`pw` path untouched.
    """
    sigs: dict[str, list[str]] = {}
    for d in definitions or []:
        lhs = d.get("lhs") or {}
        if lhs.get("type") != "apply":
            continue
        name = str(lhs.get("value"))
        args = (lhs.get("slots") or {}).get("args")
        if args is None:
            raise InductionError(f"definition of {name!r} has no args slot")
        sig = sigs.setdefault(name, ["Q"] * len(args))
        if len(sig) != len(args):
            raise InductionError(f"the definition rules for {name!r} disagree on arity")
        for i, a in enumerate(args):
            if _is_nat_ctor(a):
                sig[i] = "N"
    return sigs


def _calls(node: dict, out: set[str]) -> None:
    if node.get("type") == "apply":
        out.add(str(node.get("value")))
    for kids in (node.get("slots") or {}).values():
        for ch in kids:
            _calls(ch, out)


def _dep_order(by_name: dict[str, dict]) -> list[str]:
    """Emit each `Fixpoint` after the ones it calls — Coq has no forward reference.
    A cycle is mutual recursion (`Fixpoint … with …`), which is out of the fragment."""
    deps = {}
    for name, rules in by_name.items():
        called: set[str] = set()
        for d, _ in rules.values():
            _calls(d.get("rhs") or {}, called)
        deps[name] = {c for c in called if c in by_name and c != name}
    order: list[str] = []
    done: set[str] = set()
    active: list[str] = []

    def visit(n: str) -> None:
        if n in done:
            return
        if n in active:
            raise InductionError(
                f"mutually recursive definitions ({' / '.join(active + [n])}) are outside "
                f"the fragment")
        active.append(n)
        for c in sorted(deps[n]):
            visit(c)
        active.pop()
        done.add(n)
        order.append(n)

    for n in by_name:            # insertion order = transmission order (stable)
        visit(n)
    return order


def _guard_structural(body: dict, name: str, ridx: int, k: str) -> None:
    """Every self-recursive call must pass the match binder ITSELF in the recursion
    position. That is what makes the recursion structural, and Coq's termination
    checker rejects the whole file otherwise — which would cost us a gradeable
    request. Better to decline here, with a reason."""
    if body.get("type") == "apply" and str(body.get("value")) == name:
        args = (body.get("slots") or {}).get("args") or []
        rec = args[ridx] if ridx < len(args) else None
        if not (isinstance(rec, dict) and rec.get("type") in ("wild", "variable")
                and str(rec.get("value")) == k):
            raise InductionError(
                f"the recursive call in {name!r}'s step rule is not structural: it must recurse "
                f"on {k!r} (the predecessor bound by the S-pattern) for Coq to accept the Fixpoint")
    for kids in (body.get("slots") or {}).values():
        for ch in kids:
            _guard_structural(ch, name, ridx, k)


def _nq_def(name: str) -> str:
    """The ℕ→ℚ coercion, as a Fixpoint rather than `inject_Z ∘ Z.of_nat`: it needs
    QArith alone, and `simpl`/`cbn` turn `nq (S k)` into `1 + nq k`, which leaves
    `ring` a polynomial in the atom `nq k` instead of an opaque cast."""
    return (
        f"Fixpoint {name} (n : nat) : Q :=\n"
        f"  match n with\n"
        f"  | O => 0\n"
        f"  | S k => 1 + {name} k\n"
        f"  end.\n"
    )


def _build_apply_defs(definitions: list[dict], ctx: _Ctx) -> str:
    """One `Fixpoint` per function supplied as `apply` definitions.

    The Coq analogue of cvc5regate's `_build_apply_defs`. A Coq `Fixpoint` has ONE
    set of parameter names shared by both match branches while the transmitted base
    and step rules may use different wildcard names, so the step rule's names are
    canonical and the base rule's body is `_rename`d onto them — the same trick
    `_build_pow_def` uses.
    """
    by_name: dict[str, dict] = {}
    for d in definitions or []:
        lhs = d.get("lhs") or {}
        if lhs.get("type") != "apply":
            continue
        name = _ident(str(lhs.get("value")), "function")
        args = lhs["slots"]["args"]
        ridx = _rec_index(args)
        if ridx is None:
            raise InductionError(
                f"the definition of {name!r} matches no ℕ constructor (`0` / `S k`) in any "
                f"argument; coqregate implements ℕ recursion only")
        kind = "O" if args[ridx].get("type") == "number" else "S"
        rules = by_name.setdefault(name, {})
        if kind in rules:
            raise InductionError(f"{name!r} has two {kind}-rules")
        rules[kind] = (d, ridx)

    out = []
    for name in _dep_order(by_name):
        rules = by_name[name]
        if "O" not in rules or "S" not in rules:
            raise InductionError(
                f"the recursive function {name!r} needs exactly two rules: a base rule matching "
                f"`0` and a step rule matching `S k`")
        (base_d, bidx), (step_d, ridx) = rules["O"], rules["S"]
        if bidx != ridx:
            raise InductionError(f"{name!r} recurses on inconsistent argument positions")
        s_args = step_d["lhs"]["slots"]["args"]
        b_args = base_d["lhs"]["slots"]["args"]
        if len(b_args) != len(s_args):
            raise InductionError(f"the definition rules for {name!r} disagree on arity")

        params = [_ident(_wild_name(a), "parameter") for i, a in enumerate(s_args) if i != ridx]
        k = _ident(_wild_name(s_args[ridx]["slots"]["inner"][0]), "match binder")
        subj = _fresh("n", set(params) | {k, name, ctx.nq, FUN} | set(ctx.sigs))
        # The base rule may name its parameters differently; map them positionally.
        mapping = {}
        rest = list(params)
        for i, a in enumerate(b_args):
            if i == ridx:
                continue
            mapping[_wild_name(a)] = rest.pop(0)

        base_env = {p: "Q" for p in params}
        step_env = dict(base_env, **{k: "N"})
        base_body = _term(_rename(base_d["rhs"], mapping), "Q", ctx.scoped(base_env))
        _guard_structural(step_d["rhs"], name, ridx, k)
        step_body = _term(step_d["rhs"], "Q", ctx.scoped(step_env))

        binders, nxt = [], list(params)
        for i in range(len(s_args)):
            binders.append(f"({subj} : nat)" if i == ridx else f"({nxt.pop(0)} : Q)")
        # `{struct n}` is explicit rather than guessed: with it Coq checks the
        # recursion we intended instead of searching for one that might not exist.
        out.append(
            f"Fixpoint {name} {' '.join(binders)} {{struct {subj}}} : Q :=\n"
            f"  match {subj} with\n"
            f"  | O => {base_body}\n"
            f"  | S {k} => {step_body}\n"
            f"  end.\n"
        )
    return "\n".join(out)


def _has_pow_def(definitions: list[dict]) -> bool:
    return any((d.get("lhs") or {}).get("type") == "pow" for d in definitions or [])


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

    definitions = ex.get("definitions") or []
    # Empty unless the request uses `apply`; that is the switch between the original
    # `pow`-only emitter (unchanged, byte for byte) and the generic-function one.
    sigs = _signatures(definitions)

    env: dict[str, str] = {}
    _infer(goal, "Q", env, sigs, var if sigs else "")
    if env.get(var) != "N":
        raise InductionError(f"induction variable {var!r} must be a ℕ (exponent) variable")

    q_vars = sorted(v for v, d in env.items() if d == "Q")
    n_vars = sorted(v for v, d in env.items() if d == "N")
    fresh = next(c for c in ("k", "m", "p", "q", "i", "j") if c not in env)
    ihn = "ih" if "ih" not in env else "ih0"

    ctx = None
    if sigs:
        ctx = _Ctx(sigs, env, _fresh("nq", set(env) | set(sigs) | {FUN, THEOREM}))
        # `pw` only when something needs it — but a goal that mentions `pow` with no
        # `pow` definitions still raises here rather than emitting a dangling `pw`.
        needs_pow = _has_pow_def(definitions) or _mentions(goal, "pow")
        blocks = [_build_pow_def(definitions, ctx)] if needs_pow else []
        blocks.append(_build_apply_defs(definitions, ctx))
    else:
        blocks = [_build_pow_def(definitions)]
    lhs = _term(goal["slots"]["left"][0], "Q", ctx)
    rhs = _term(goal["slots"]["right"][0], "Q", ctx)
    if ctx is not None and ctx.need_nq:      # only once we know something coerced
        blocks.insert(0, _nq_def(ctx.nq))
    pow_def = "\n".join(b for b in blocks if b)

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
    header = ("From Coq Require Import QArith.\n"
              "From Coq Require Import Arith.\n"
              "From Coq Require Import Lia.\n"
              "Open Scope Q_scope.\n\n")
    if ctx is None:
        return (
            # `From Coq Require` works on both Coq 8.x and Rocq 9.x (deprecated-with-
            # warning on 9.x, which coq_prover silences). Stdlib only — no Mathlib.
            header +
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

    # ---- the `apply` variant of the same proof ----------------------------
    # Two differences, both forced by generic recursive functions:
    #
    # (1) `revert` the ℚ parameters before inducting, so the inductive hypothesis is
    #     `∀x⃗. P(x⃗, k)` rather than P at the accumulator the student started with.
    #     An accumulator-carrying function (`fact_aux x (S k) = fact_aux (x·(S k)) k`)
    #     needs the IH at a SHIFTED accumulator, which a fixed-x IH cannot supply.
    #     The statement proved is identical; only the induction is generalized.
    # (2) `cbn [f …]` instead of bare `simpl`: unfold exactly the functions we
    #     emitted (including the ℕ→ℚ coercion) and leave everything else alone, so
    #     `ring` sees the recursive calls as atoms rather than an unfolded ℚ pair.
    unfold = ([ctx.nq] if ctx.need_nq else []) + ([FUN] if _has_pow_def(definitions) else []) \
        + sorted(sigs)
    norm = (f"repeat rewrite Nat.add_succ_r; repeat rewrite Nat.add_0_r; "
            f"cbn [{' '.join(unfold)}]")
    close = (f"first [ ring | rewrite {ihn}; ring | rewrite <- {ihn}; ring "
             f"| (ring_simplify; rewrite {ihn}; ring) "
             f"| (simpl; ring) | (simpl; rewrite {ihn}; ring) | (field; lia) ]")
    revert = f"  revert {' '.join(q_vars)}.\n" if q_vars else ""
    reintro = f"intros {' '.join(q_vars)}; " if q_vars else ""
    return (
        header +
        f"{pow_def}\n"
        f"Theorem {THEOREM} : forall {binders}, {lhs} == {rhs}.\n"
        f"Proof.\n"
        f"  intros {intro}.\n"
        f"{revert}"
        f"  induction {var} as [| {fresh} {ihn}].\n"
        f"  - {reintro}{norm}; {close}.\n"
        f"  - {reintro}{norm}; {close}.\n"
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
# That warrant is only worth what enforces it, so `options.verify_rules`
# re-establishes it from scratch — each rule gets its own Coq kernel run with an
# automatic tactic. Use it for rules from a source you have not yet validated, or
# in CI. Regate does not run a caller-supplied proof script (that is an injection
# surface, and rule soundness is the caller's upstream job), so a `proof` field on
# a rule is ignored; a rule outside the automatic fragment is simply unproven.
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
    # "ring"     -- the kernel proved it from scratch
    method: str      # …| "rejected" | "guarded" | "unavailable" | "untranslatable"
    detail: str = ""


def verify_rules_enabled(ex: dict) -> bool:
    """Should the transmitted ruleset be re-verified rather than trusted?"""
    return bool((ex.get("options") or {}).get("verify_rules"))


def build_rule_source(rule: dict, definitions: list[dict] | None = None) -> str:
    """A standalone Coq file proving `forall vars, lhs == rhs` for one rule.

    Regate does not accept a caller-supplied proof script (that is an injection
    surface, and rule soundness is the caller's upstream responsibility): the rule
    is discharged by an automatic tactic here, or it is simply unproven.
    """
    lhs_node, rhs_node = rule.get("lhs"), rule.get("rhs")
    if not lhs_node or not rhs_node:
        raise InductionError("rule needs lhs and rhs")

    definitions = definitions or []
    sigs = _signatures(definitions)
    env: dict[str, str] = {}
    _infer(lhs_node, "Q", env, sigs)
    _infer(rhs_node, "Q", env, sigs)

    # A rule that mentions `apply` needs the functions in scope to even state it.
    ctx = None
    if sigs and (_mentions(lhs_node, "apply") or _mentions(rhs_node, "apply")):
        ctx = _Ctx(sigs, env, _fresh("nq", set(env) | set(sigs) | {FUN, RULE_THEOREM}))
    lhs, rhs = _term(lhs_node, "Q", ctx), _term(rhs_node, "Q", ctx)
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
    if _mentions(lhs_node, "pow") or _mentions(rhs_node, "pow"):
        pow_def = _build_pow_def(definitions, ctx) + "\n"
    if ctx is not None:
        pow_def += _build_apply_defs(definitions, ctx) + "\n"
        if ctx.need_nq:
            pow_def = _nq_def(ctx.nq) + "\n" + pow_def

    forall = f"forall {binders}, " if binders else ""
    body = "first [ ring | simpl; ring | field | (field; lia) | (simpl; field) ]"
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


def _mentions(node: dict, type_: str) -> bool:
    """Does this node type occur anywhere in the tree? (`pow` -> needs `pw`;
    `apply` -> needs the emitted Fixpoints.)"""
    if node.get("type") == type_:
        return True
    return any(_mentions(ch, type_)
               for children in (node.get("slots") or {}).values() for ch in children)


_RULE_CACHE: dict[str, ProvenRule] = {}


def prove_rule(rule: dict, definitions: list[dict] | None = None) -> ProvenRule:
    """Kernel-prove one transmitted rule with an automatic tactic. Unproven is
    inconclusive, not false. A caller-supplied `proof` field is ignored — Regate
    does not run untrusted proof scripts. Only called when `verify_rules` is set.
    """
    rid = str(rule.get("id", "?"))
    if rule.get("conditions"):
        # A guarded rule (`x/x = 1` needing `x != 0`) is not an unconditional
        # equality; we do not model the side condition, so we cannot prove it.
        # (step_check refuses guarded rules independently, trusted or not.)
        return ProvenRule(rid, False, "guarded",
                          "guarded rules are outside the certifiable fragment")

    try:
        source = build_rule_source(rule, definitions)
    except InductionError as e:
        return ProvenRule(rid, False, "untranslatable", str(e))

    key = hashlib.sha256(source.encode()).hexdigest()
    if key in _RULE_CACHE:
        return _RULE_CACHE[key]
    if not coq_prover.coq_available():
        return ProvenRule(rid, False, "unavailable", "coq toolchain unavailable")

    ok, detail = coq_prover.check_source(source)
    result = ProvenRule(rid, True, "ring") if ok else ProvenRule(rid, False, "rejected", detail[:400])
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


def _uses_generalized_ih(steps: list[dict], ih: tuple[dict, dict], ac: tuple) -> str:
    """Does the student instantiate the IH at a SHIFTED accumulator?

    The emitted Coq proof reverts the ℚ parameters before inducting, so its IH is
    `∀x⃗. P(x⃗, k)` and applying it at `x·(S k)` is sound — but coqregate's symbolic
    step checker only recognises the IH literally, at the induction variable (there
    is no `generalize_ih` in this clone of step_check). Certifying such a derivation
    would mean trusting a step we never checked; calling it `invalid` would be the
    exact false negative M1 fixed. So decline: `uncertifiable` ⇒ `unknown`.

    Only consulted for `apply` requests, where accumulator-carrying functions make
    the generalized IH the normal shape; the ℕ-exponent path is untouched.
    """
    for i, s in enumerate(steps or []):
        if s.get("kind") != "B":
            continue
        eqn = s.get("equation")
        if not (isinstance(eqn, list) and len(eqn) == 2):
            continue                       # malformed: let the strict checker judge it
        forward = (step_check.ac_equal(eqn[0], ih[0], ac)
                   and step_check.ac_equal(eqn[1], ih[1], ac))
        backward = (step_check.ac_equal(eqn[0], ih[1], ac)
                    and step_check.ac_equal(eqn[1], ih[0], ac))
        if forward or backward:
            continue
        return (f"step {i} applies the inductive hypothesis at a shifted accumulator (a "
                f"generalized IH); the Coq proof generalizes it, but coqregate's step checker "
                f"only certifies the IH at the induction variable itself")
    return ""


def grade_derivation(ex: dict, sub: dict) -> GradeResult:
    goal = ex.get("goal")
    var = ex.get("inductionVar")
    if not goal or goal.get("type") != "eq" or not var:
        return GradeResult("untranslatable", "goal must be an equality with an inductionVar")
    var = str(var)

    # Decline vocabulary Coqregate cannot translate to its kernel (a non-ℕ datatype,
    # a function whose definitions do not form a Coq Fixpoint) BEFORE symbolic
    # step-checking. Otherwise the strict rule-instance checker runs on an
    # untranslatable goal and reports a misleading `invalid_derivation` on a student
    # derivation it never actually certifies. Unimplemented ⇒ `unknown`, not `invalid`.
    definitions = ex.get("definitions") or []
    try:
        sigs = _signatures(definitions)
        if sigs:
            # `apply` in play: the whole certificate has to be emittable — the goal
            # AND every `Fixpoint` — not just the goal's two sides, since a function
            # we cannot define is a goal we can never certify.
            build_source(ex)
        else:
            _infer(goal, "Q", {})
            _term(goal["slots"]["left"][0], "Q")
            _term(goal["slots"]["right"][0], "Q")
    except (InductionError, KeyError, IndexError, TypeError) as e:
        return GradeResult("untranslatable", f"goal is outside Coqregate's fragment: {e}")

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
    ih = (goal["slots"]["left"][0], goal["slots"]["right"][0])
    if sigs:
        # Decline a derivation that needs a generalized IH BEFORE grading any part of
        # it: the request as a whole is outside what this backend can certify, and
        # half-grading it would report an `invalid` we cannot stand behind.
        shifted = _uses_generalized_ih(step_steps, ih, ac)
        if shifted:
            return GradeResult("uncertifiable", f"inductive step: {shifted}", ruleset=ruleset_meta)
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
