from __future__ import annotations

import hashlib
from dataclasses import dataclass

import cvc5_induction as ci
import cvc5_prover

# The non-induction equivalence oracle. cvc5regate's induction path proves
# `∀n. P(n)`; this proves plain algebraic equivalence `source ≡ target` (and its
# refutation), reusing the same MathNode→SMT translator. Disprove-FIRST (a numeric
# counterexample is the most useful, always-sound thing to return), then prove.
#
# The prove query is exactly the one `cvc5_induction.build_rule_source` already
# builds for a transmitted rule — an equality universally-quantified over its free
# variables — so we synthesise a rule `{lhs: source, rhs: target}` and reuse it.
# The disprove query needs the induction module's low-level translator helpers.

InductionError = ci.InductionError


@dataclass
class EquivResult:
    # outcome maps onto the protocol as in cvc5_induction.CertifyResult.
    outcome: str          # "proven_equal" | "proven_unequal" | "equal_no_certificate" | "unknown"
    certified: bool
    method: str           # "alethe+carcara" | "validity" | "fmf-fun" | "rejected" | "unavailable" | "untranslatable"
    witness: dict | None = None
    smtlib: str = ""       # the accepted prove-source (re-runnable certificate)
    alethe: str | None = None
    rechecked: bool = False
    detail: str = ""


def build_prove_source(ex: dict, source: dict, target: dict) -> str:
    """Validity query for `source = target`: reuse the rule prover's builder."""
    return ci.build_rule_source({"id": "equiv", "lhs": source, "rhs": target}, ex)


def build_disprove_source(ex: dict, source: dict, target: dict) -> tuple[str, list[str]]:
    """Counterexample search for `source = target`: the free variables are constants
    and cvc5 (with `--fmf-fun`) hunts a model where the two sides differ. Also
    returns the `get-value` labels naming the witness."""
    env: dict[str, str] = {}
    ci._infer(source, "Q", env)
    ci._infer(target, "Q", env)

    sort = ci._numsort(ex, ex.get("goal") or {"type": "eq"})
    ctx = ci._Ctx(sort, env)

    definitions = ex.get("definitions") or []
    defs = ""
    if ci._mentions(source, ("pow",)) or ci._mentions(target, ("pow",)):
        defs += ci._build_pow(definitions, ctx)
    if ci._mentions(source, ("apply",)) or ci._mentions(target, ("apply",)):
        defs += ci._build_apply_defs(definitions, ctx)

    lhs = ci._term(source, ctx)
    rhs = ci._term(target, ctx)

    n_vars = sorted(v for v, d in env.items() if d == "N")
    q_vars = sorted(v for v, d in env.items() if d == "Q")
    # A ℕ-tagged variable is read back numerically as `(val n)`; `val` must exist even
    # if the body never coerced one (mirrors build_disprove_source's force_val).
    ctx.need_val = ctx.need_val or bool(n_vars)
    preamble = ci._preamble(ctx, defs)

    decls = [f"(declare-const {v} {sort})" for v in q_vars]
    decls += [f"(declare-const {v} Nat)" for v in n_vars]
    labels = q_vars + n_vars
    getvals = " ".join((f"(val {v})" if v in n_vars else v) for v in labels)
    body = (preamble + "\n".join(decls) + "\n"
            f"(assert (not (= {lhs} {rhs})))\n"
            "(check-sat)\n")
    if labels:
        body += f"(get-value ({getvals}))\n"
    return body, labels


_CACHE: dict[str, EquivResult] = {}


def decide_equivalence(ex: dict, source: dict, target: dict) -> EquivResult:
    """Decide `source ≡ target` with cvc5. Disprove-first (cheap counterexample
    search), then prove with an optionally Carcara-re-checked Alethe certificate."""
    try:
        prove_src = build_prove_source(ex, source, target)
        dis_src, labels = build_disprove_source(ex, source, target)
    except InductionError as e:
        return EquivResult("unknown", False, "untranslatable", detail=str(e))

    key = hashlib.sha256((prove_src + str(ci.REQUIRE_RECHECK)).encode()).hexdigest()
    if key in _CACHE:
        return _CACHE[key]
    if not cvc5_prover.cvc5_available():
        return EquivResult("unknown", False, "unavailable", detail="cvc5 toolchain unavailable")

    # 1) Disprove first — a numeric counterexample, when one exists.
    dis = cvc5_prover.disprove(dis_src, labels)
    if dis.verdict == "sat" and ci._usable_witness(dis.witness, labels):
        return _store(key, EquivResult("proven_unequal", True, "fmf-fun",
                                       witness=dis.witness,
                                       detail="cvc5 found a counterexample"))

    # 2) Prove the equivalence (plain solving), with an optional Alethe+Carcara re-check.
    res = cvc5_prover.prove_equiv(prove_src, want_certificate=True)
    if res.verdict == "unsat":
        if res.rechecked:
            return _store(key, EquivResult("proven_equal", True, "alethe+carcara",
                                           smtlib=prove_src, alethe=res.alethe, rechecked=True,
                                           detail="cvc5 proof re-checked by Carcara"))
        if ci.REQUIRE_RECHECK:
            return _store(key, EquivResult("equal_no_certificate", False, "validity",
                                           smtlib=prove_src,
                                           detail="cvc5 proved it but no independently "
                                                  "re-checked Alethe certificate is available"))
        return _store(key, EquivResult("proven_equal", True, "validity", smtlib=prove_src,
                                       detail="proved equivalent by cvc5"))
    if dis.verdict == "sat":
        # Refuted, but the counterexample is unreportable (e.g. a datatype term) — honest
        # "unequal but no numeric witness" degrades to unknown, never a witness-less
        # proven_unequal (protocol invariant).
        return _store(key, EquivResult("unknown", False, "rejected",
                                       detail="cvc5 refuted equivalence but produced no numeric witness"))
    return _store(key, EquivResult("unknown", False, "rejected", detail=res.detail[:600]))


def _store(key: str, result: EquivResult) -> EquivResult:
    _CACHE[key] = result
    return result


# ---------------------------------------------------------------------------
# Structural distance for partial credit (equivalent, but not yet in target form).
# A small stdlib-only tree metric — cvc5regate shares no code with eggregate's
# model.distance, only the idea: count the nodes that differ between two trees.
# ---------------------------------------------------------------------------
def _size(node: dict) -> int:
    return 1 + sum(_size(c) for kids in (node.get("slots") or {}).values() for c in kids)


def distance(a: dict, b: dict) -> int:
    """Number of differing nodes: 0 iff structurally identical. Two trees with the
    same shape are compared child-by-child; a shape/label mismatch counts the whole
    of both subtrees (an insert+delete)."""
    if a == b:
        return 0
    sa = a.get("slots") or {}
    sb = b.get("slots") or {}
    if a.get("type") != b.get("type") or a.get("value") != b.get("value") \
            or sorted(sa) != sorted(sb) or any(len(sa[k]) != len(sb[k]) for k in sa):
        return _size(a) + _size(b)
    d = 0
    for k in sa:
        for ca, cb in zip(sa[k], sb[k]):
            d += distance(ca, cb)
    return d
