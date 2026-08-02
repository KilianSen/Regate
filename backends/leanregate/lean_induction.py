from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass

import lean_prover  # reuse the kernel seam: _run_lean, lean_available, caching style

FUN = "pw"           # the Lean name for the model's `pow` node
THEOREM = "regate_induction"
# Emitted names for `apply` functions are prefixed, so a request naming its function
# `sum`/`max`/`id` cannot collide with a Mathlib root declaration (a collision is only
# a Lean error -> `unknown`, but the prefix keeps the emitted file readable).
FUN_PREFIX = "rg_"


class InductionError(ValueError):
    """The induction goal/definitions are outside the supported Lean fragment."""


# ---------------------------------------------------------------------------
# Identifiers.
#
# Every name in the emitted source comes from caller-supplied JSON, so it is
# checked before it reaches the file: Regate emits Lean that the kernel must check
# itself, and a name containing whitespace/brackets/`:=` could otherwise close the
# term and open a *new* declaration (`sorry` elaborates with exit code 0, i.e. it
# would certify anything). Rejecting is fail-safe: InductionError -> untranslatable
# -> `unknown`.
# ---------------------------------------------------------------------------
def _ident(name: str, what: str) -> str:
    if not name or name[0].isdigit() or not all(c.isalnum() or c in "_'" for c in name):
        raise InductionError(f"{what} {name!r} is not a usable Lean identifier")
    return name


def _fun_name(name: str) -> str:
    return FUN_PREFIX + _ident(name, "function name")


# ---------------------------------------------------------------------------
# `apply` — n-ary NAMED function application (protocol 1.1).
#
# `apply` carries no meaning of its own: a function is defined by exactly two
# transmitted `definitions` rules, one matching the datatype's base constructor and
# one matching its step constructor, recursing on the constructor-matched argument
# — which may be ANY position, not necessarily the last. This is the ℕ-only reading
# of that contract (`0` / `succ k`), matching leanregate's ℚ-goal/ℕ-exponent typing;
# `exercise.datatype` (lists, trees) is declined in `check_translatable`.
# ---------------------------------------------------------------------------
def _args(apply_node: dict) -> list:
    args = (apply_node.get("slots") or {}).get("args")
    if not isinstance(args, list):
        raise InductionError(f"apply node {apply_node.get('value')!r} has no 'args' slot")
    return args


def _is_zero(node: dict) -> bool:
    return node.get("type") == "number" and str(node.get("value")).strip() == "0"


def _apply_rules(definitions: list[dict]) -> dict[str, tuple]:
    """`{fn: (base_rule, step_rule, rec_index, arity)}` for every function defined by
    `apply` rules. Exactly two rules per function: `f(…, 0, …)` and `f(…, succ k, …)`
    matching in the SAME argument position."""
    grouped: dict[str, list[dict]] = {}
    for d in definitions:
        lhs = d.get("lhs") or {}
        if lhs.get("type") != "apply":
            continue
        grouped.setdefault(str(lhs.get("value", "")), []).append(d)
    out: dict[str, tuple] = {}
    for name, rules in grouped.items():
        _ident(name, "function name")
        hits = [(d, i) for d in rules for i, a in enumerate(_args(d["lhs"]))
                if a.get("type") == "succ"]
        if len(hits) != 1:
            raise InductionError(
                f"{name!r} needs exactly one step rule matching `succ` in exactly one "
                f"argument position (found {len(hits)})")
        step_rule, idx = hits[0]
        arity = len(_args(step_rule["lhs"]))
        bases = [d for d in rules
                 if d is not step_rule and len(_args(d["lhs"])) == arity
                 and _is_zero(_args(d["lhs"])[idx])]
        if len(rules) != 2 or len(bases) != 1:
            raise InductionError(
                f"{name!r} needs exactly two definitions: a base rule with 0 and a step "
                f"rule with `succ k` in argument {idx}")
        out[name] = (bases[0], step_rule, idx, arity)
    return out


def _signatures(funs: dict[str, tuple]) -> dict[str, list[str]]:
    """function name → per-argument domain: "N" at the recursion position, "Q" else."""
    return {name: ["N" if i == idx else "Q" for i in range(arity)]
            for name, (_b, _s, idx, arity) in funs.items()}


def _sig_of(name: str, sigs: dict | None, args: list, dom: str) -> list[str]:
    sig = (sigs or {}).get(name)
    if sig is None:
        raise InductionError(f"no recursive definition for function {name!r}")
    if len(args) != len(sig):
        raise InductionError(
            f"{name!r} is applied to {len(args)} argument(s) but defined with {len(sig)}")
    if dom != "Q":
        # v1 functions return ℚ, so an `apply` cannot stand in a ℕ position (an
        # exponent, or another function's recursion argument).
        raise InductionError(f"function {name!r} returns a ℚ value and cannot appear in a ℕ position")
    return sig


# ---------------------------------------------------------------------------
# Typing: which variables are ℕ (exponents / the induction var) vs ℚ.
# `indvar` is ALWAYS ℕ (we induct on it structurally) and is exempt from the
# ℚ/ℕ consistency check: where it appears numerically it is cast, `(n : ℚ)`.
# ---------------------------------------------------------------------------
def _infer(node: dict, dom: str, env: dict[str, str],
           sigs: dict | None = None, indvar: str = "") -> None:
    t = node.get("type")
    if t == "variable":
        name = str(node["value"])
        if name == indvar:
            env[name] = "N"
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
    elif t == "apply":
        name = str(node.get("value", ""))
        args = _args(node)
        for a, d in zip(args, _sig_of(name, sigs, args, dom)):
            _infer(a, d, env, sigs, indvar)
    elif t == "eq":
        _infer(s["left"][0], "Q", env, sigs, indvar)
        _infer(s["right"][0], "Q", env, sigs, indvar)
    else:
        raise InductionError(f"cannot type node type {t!r}")


# ---------------------------------------------------------------------------
# MathNode -> Lean term, domain-aware (ℚ or ℕ).
#
# `env` (variable → "Q"/"N") is optional: when supplied, a ℕ variable standing in a
# ℚ position is cast — `(n : ℚ)` — which is what a goal like `2·sum n = n·(n+1)`
# needs. `Nat.cast` is a ring hom, so the cast reading is faithful.
# ---------------------------------------------------------------------------
_BIN = {"add": "+", "sub": "-", "mul": "*"}


def _term(node: dict, dom: str, sigs: dict | None = None, env: dict | None = None) -> str:
    t = node.get("type")
    if t in ("variable", "wild"):
        name = _ident(str(node["value"]), "variable")
        if dom == "Q" and (env or {}).get(name) == "N":
            return f"({name} : ℚ)"
        return name
    if t == "number":
        return f"({node['value']} : {'ℚ' if dom == 'Q' else 'ℕ'})"
    s = node["slots"]
    if t == "succ":
        # In a ℚ position the predecessor must be cast first: `((k : ℚ) + 1)`, never
        # `(k + 1)` — the latter is a ℕ term that only elaborates by accident.
        inner = _term(s["inner"][0], "N", sigs, env)
        return f"(({inner} : ℚ) + 1)" if dom == "Q" else f"({inner} + 1)"
    if t == "pow":
        return f"({FUN} {_term(s['base'][0], 'Q', sigs, env)} {_term(s['exponent'][0], 'N', sigs, env)})"
    if t in _BIN:
        if t == "sub" and dom == "N":
            # ℕ subtraction is TRUNCATED (`2 - 3 = 0`). Emitting it would have Lean
            # certify a different statement than the one the host asked about, so
            # decline instead of silently changing the claim.
            raise InductionError("subtraction in a ℕ position is truncating; not translated")
        return (f"({_term(s['left'][0], dom, sigs, env)} {_BIN[t]} "
                f"{_term(s['right'][0], dom, sigs, env)})")
    if t == "frac":
        return (f"({_term(s['numerator'][0], 'Q', sigs, env)} / "
                f"{_term(s['denominator'][0], 'Q', sigs, env)})")
    if t == "neg":
        return f"(-{_term(s['inner'][0], dom, sigs, env)})"
    if t == "apply":
        name = str(node.get("value", ""))
        args = _args(node)
        sig = _sig_of(name, sigs, args, dom)
        parts = " ".join(_term(a, d, sigs, env) for a, d in zip(args, sig))
        return f"({_fun_name(name)} {parts})" if parts else _fun_name(name)
    raise InductionError(f"cannot translate node type {t!r}")


# ---------------------------------------------------------------------------
# The recursive `pow` definition, derived from the transmitted definitions.
# ---------------------------------------------------------------------------
def _wild_name(node: dict) -> str:
    if node.get("type") != "wild":
        raise InductionError("expected a wildcard in the definition pattern")
    return str(node["value"])


def _build_pow_def(definitions: list[dict]) -> str:
    """`def pw : ℚ → ℕ → ℚ` from the `pow(a,0)→…` and `pow(a,S n)→…` rules."""
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
        raise InductionError("pow needs a base rule (pow(a,0)→…) and a successor rule (pow(a,S n)→…)")

    b_var = _wild_name(base_rule["lhs"]["slots"]["base"][0])
    base_body = _term(base_rule["rhs"], "Q")

    s_var = _wild_name(succ_rule["lhs"]["slots"]["base"][0])
    rec_var = _wild_name(succ_rule["lhs"]["slots"]["exponent"][0]["slots"]["inner"][0])
    succ_body = _term(succ_rule["rhs"], "Q")
    return (
        f"def {FUN} : ℚ → ℕ → ℚ\n"
        f"  | {b_var}, 0 => {base_body}\n"
        f"  | {s_var}, ({rec_var} + 1) => {succ_body}\n"
    )


# ---------------------------------------------------------------------------
# The `apply` functions as structurally-recursive Lean `def`s — the analogue of
# `_build_pow_def`, driven entirely by the transmitted `definitions`.
#
# This is where Lean's kernel earns its keep: a `def` is admitted only if the
# equation compiler finds it structurally terminating, so a bogus "definition"
# cannot be used to derive False — it is a compile error, i.e. `unknown`.
# ---------------------------------------------------------------------------
def _pat_name(node: dict) -> str:
    """A pattern variable in a definition's LHS (`wild`, or `variable` for hosts
    that spell parameters that way)."""
    if node.get("type") not in ("wild", "variable"):
        raise InductionError("expected a pattern variable in the definition pattern")
    return _ident(str(node["value"]), "pattern variable")


def _emit_order(funs: dict[str, tuple], roots: set) -> list[str]:
    """Emission order for the functions the goal actually reaches: a function comes
    after everything it calls. Mutual recursion needs a Lean `mutual` block and is
    declined. Unreached definitions are simply not emitted — a request may transmit
    a whole exercise family's definitions."""
    calls = {name: _called(rules[1]["rhs"]) | _called(rules[0]["rhs"])
             for name, rules in funs.items()}
    order: list[str] = []
    state: dict[str, int] = {}

    def visit(n: str) -> None:
        if state.get(n) == 2:
            return
        if state.get(n) == 1:
            raise InductionError(f"mutually recursive definitions ({n!r}) are not supported")
        state[n] = 1
        for dep in sorted(calls.get(n, set())):
            if dep != n and dep in funs:
                visit(dep)
        state[n] = 2
        order.append(n)

    for name in sorted(roots):
        if name in funs:
            visit(name)
    return order


def _called(node: dict) -> set:
    """Every function name applied in `node`."""
    if not isinstance(node, dict):
        return set()
    names = {str(node["value"])} if node.get("type") == "apply" else set()
    for kids in (node.get("slots") or {}).values():
        for k in kids:
            names |= _called(k)
    return names


def _build_apply_defs(funs: dict[str, tuple], sigs: dict, order: list[str]) -> str:
    """One `def` per `apply` function, pattern-matching the recursion argument at
    whatever position the definitions match it in (not necessarily the last)."""
    out = []
    for name in order:
        base_rule, step_rule, idx, arity = funs[name]
        sig = sigs[name]
        arrow = " → ".join(["ℚ" if d == "Q" else "ℕ" for d in sig] + ["ℚ"])

        def alt(rule: dict, rec_pat: str) -> str:
            args = _args(rule["lhs"])
            # Each alternative binds its OWN pattern names (Lean's equation compiler),
            # so the base and step rules need not agree on parameter names.
            local = {}
            pats = []
            for i, a in enumerate(args):
                if i == idx:
                    pats.append(rec_pat)
                    continue
                pname = _pat_name(a)
                local[pname] = "Q"
                pats.append(pname)
            if idx < len(args) and args[idx].get("type") == "succ":
                local[_pat_name(args[idx]["slots"]["inner"][0])] = "N"
            return f"  | {', '.join(pats)} => {_term(rule['rhs'], 'Q', sigs, local)}\n"

        rec_var = _pat_name(_args(step_rule["lhs"])[idx]["slots"]["inner"][0])
        out.append(f"def {_fun_name(name)} : {arrow}\n"
                   + alt(base_rule, "0")
                   + alt(step_rule, f"({rec_var} + 1)"))
    return "".join(out)


def _mentions(node, types: tuple) -> bool:
    if not isinstance(node, dict):
        return False
    if node.get("type") in types:
        return True
    return any(_mentions(c, types)
               for kids in (node.get("slots") or {}).values() for c in kids)


def check_translatable(ex: dict) -> None:
    """Raise `InductionError` if this induction exercise is outside leanregate's
    Lean fragment. `grade.py` calls this BEFORE the symbolic step-check, so
    unimplemented vocabulary declines as `unknown` instead of being mis-graded
    `invalid_derivation` (the M1/M2 false-negative class)."""
    if ex.get("datatype"):
        raise InductionError("datatype induction (exercise.datatype) is not implemented; "
                             "leanregate supports ℕ (zero/succ) induction only")
    goal = ex.get("goal") or {}
    sigs = _signatures(_apply_rules(ex.get("definitions") or []))
    var = str(ex.get("inductionVar") or "")
    env: dict[str, str] = {var: "N"} if var else {}
    _infer(goal, "Q", env, sigs, var)
    _term(goal["slots"]["left"][0], "Q", sigs, env)
    _term(goal["slots"]["right"][0], "Q", sigs, env)


# ---------------------------------------------------------------------------
# The whole Lean file: definition + theorem + induction proof.
# ---------------------------------------------------------------------------
def build_source(ex: dict) -> str:
    goal = ex.get("goal")
    if not goal or goal.get("type") != "eq":
        raise InductionError("induction goal must be an equality")
    var = ex.get("inductionVar")
    if not var:
        raise InductionError("missing inductionVar")
    if ex.get("datatype"):
        raise InductionError("datatype induction (exercise.datatype) is not implemented; "
                             "leanregate supports ℕ (zero/succ) induction only")

    definitions = ex.get("definitions") or []
    funs = _apply_rules(definitions)
    sigs = _signatures(funs)

    env: dict[str, str] = {str(var): "N"}
    _infer(goal, "Q", env, sigs, str(var))
    if env.get(var) != "N":
        raise InductionError(f"induction variable {var!r} must be a ℕ (exponent) variable")

    q_vars = sorted(v for v, d in env.items() if d == "Q")
    n_vars = sorted(v for v, d in env.items() if d == "N")
    fresh = next(c for c in ("k", "m", "p", "q", "i", "j") if c not in env)
    ihn = "ih" if "ih" not in env else "ih0"

    # `pw` is emitted when the request defines `pow` — or when the goal/definitions
    # use a `pow` node without defining it, which keeps that request's existing
    # decline. An `apply`-only exercise needs no `pw` at all.
    defs = ""
    names: list[str] = []
    if (any(d.get("lhs", {}).get("type") == "pow" for d in definitions)
            or _mentions(goal, ("pow",))
            or any(_mentions(d.get("rhs"), ("pow",)) for d in definitions)):
        defs += _build_pow_def(definitions)
        names.append(FUN)
    order = _emit_order(funs, _called(goal))
    defs += _build_apply_defs(funs, sigs, order)
    names += [_fun_name(n) for n in order]
    # Definition lemma list for `simp`; empty stays empty rather than `simp_all []`.
    lemmas = ", ".join(names)
    lst = f" [{lemmas}]" if lemmas else ""
    unfold = ", ".join(names + ["Nat.add_eq"])
    closing = ", ".join(names + [ihn])
    # An accumulator function (`fact_aux x n = x * fact n`) needs the IH universal in
    # its accumulators — exactly what cvc5 gets by co-quantifying them. In Lean that
    # is `induction n generalizing x`. Only emitted for `apply` exercises, so the
    # `pow` path's proof script is unchanged byte for byte.
    others = [v for v in q_vars + n_vars if v != var]
    gen = f" generalizing {' '.join(others)}" if order and others else ""
    # Casts appear as soon as a ℕ variable is used numerically (`(n : ℚ)`); after
    # `induction` the goal holds `↑(k+1)`, which only `ring`s once `push_cast` has
    # pushed the cast inward. Extra `first` alternatives, tried after the existing
    # ones, so nothing that closed before closes differently now.
    cast = (f" | (rw [{ihn}]; push_cast; ring)"
            f" | (simp only [{ihn}]; push_cast; ring)") if order else ""
    zcast = f" | (simp{lst}; push_cast; ring)" if order else ""

    lhs = _term(goal["slots"]["left"][0], "Q", sigs, env)
    rhs = _term(goal["slots"]["right"][0], "Q", sigs, env)
    binders = ""
    if q_vars:
        binders += f" ({' '.join(q_vars)} : ℚ)"
    binders += f" ({' '.join(n_vars)} : ℕ)"
    intro = " ".join(q_vars + n_vars)
    return (
        # The ℚ + tactic-suite imports the prover's auto-prove path uses, so they
        # are guaranteed present in the (pruned) build cache.
        "import Mathlib.Data.Rat.Defs\n"
        "import Mathlib.Tactic\n\n"
        f"{defs}\n"
        f"theorem {THEOREM} :∀{binders}, {lhs} = {rhs} := by\n"
        f"  intro {intro}\n"
        f"  induction {var}{gen} with\n"
        f"  | zero => first | simp_all{lst} | (simp{lst}; ring){zcast} | ring\n"
        # Unfold `pw` and normalise the `m.add k` that a `m + (k+1)` exponent leaves
        # back to `m + k` (`Nat.add_eq`), so the forward IH rewrite matches. Then try,
        # cheapest first: forward `rw [{ihn}]` (closes e.g. `1ⁿ=1`, `aᵐ⁺ⁿ=aᵐ·aⁿ`),
        # then the backward fold `rw [← {ihn}]` (closes `aⁿ·bⁿ=(a·b)ⁿ` by folding the
        # product under one `pow`). The fold is reached ONLY after the forward rewrite
        # fails, so it never loops on a goal whose IH has a literal RHS. All branches
        # are sound; `first` takes whichever closes. (Verified on Lean v4.32.0-rc1 + Mathlib.)
        # `all_goals` so the IH-closing block is a no-op when `simp only` already
        # discharged the goal (e.g. a reflexive or IH-free succ case) — otherwise the
        # trailing `first` would error with "no goals to be solved".
        f"  | succ {fresh} {ihn} => simp only [{unfold}]; all_goals (first"
        f" | (rw [{ihn}]; ring)"
        f" | (rw [← {ihn}]; ring)"
        f" | (simp only [{ihn}]; ring)"
        f" | (simp only [← {ihn}]; ring)"
        f"{cast}"
        f" | simp_all [{closing}])\n"
    )


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
    """Certify `∀ inductionVar. goal` with a Lean `induction` kernel run."""
    try:
        source = build_source(ex)
    except (InductionError, KeyError, IndexError, TypeError) as e:
        # A malformed `definitions` entry (no `rhs`, a non-list `args`) is a decline,
        # not a crash: an escaped exception would be an HTTP 500 / exit 1.
        return CertifyResult(False, "untranslatable", str(e))

    key = hashlib.sha256(source.encode()).hexdigest()
    if key in _CACHE:
        return _CACHE[key]
    if not lean_prover.lean_available():
        return CertifyResult(False, "unavailable", "lean toolchain unavailable")

    ok, detail = lean_prover._run_lean(source)
    result = CertifyResult(True, "induction") if ok else CertifyResult(False, "rejected", detail)
    _CACHE[key] = result
    return result
