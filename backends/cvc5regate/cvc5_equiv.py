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

# NOT `InductionError = ci.InductionError`. Binding the class object here captures
# whichever class existed at import time; `importlib.reload(cvc5_induction)` (the
# test harness does this to drop its stubs) rebuilds the class, after which a
# captured alias no longer matches what cvc5_induction raises — the `except` below
# silently stops catching and the error escapes `grade()` as an HTTP 500 / exit 1,
# which the protocol forbids. Resolving `ci.InductionError` at raise/except time
# always tracks the live class.
def _induction_error(*args) -> Exception:
    return ci.InductionError(*args)


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
    """Validity query for `source = target`: reuse the rule prover's builder, with the
    exercise's declared `assumptions` as hypotheses (`use_assumptions=True`).

    They are not optional here: SMT-LIB division is underspecified at 0, so `x/x = 1`
    is *not* valid unquantified — it is a theorem exactly under `x ≠ 0`. An assumption
    kind with no sound translation raises `InductionError`, and the query declines to
    `unknown` rather than proceeding without it."""
    return ci.build_rule_source({"id": "equiv", "lhs": source, "rhs": target}, ex,
                                use_assumptions=True)


def build_disprove_source(ex: dict, source: dict, target: dict) -> tuple[str, list[str]]:
    """Counterexample search for `source = target`: the free variables are constants
    and cvc5 (with `--fmf-fun`) hunts a model where the two sides differ. Also
    returns the `get-value` labels naming the witness.

    The exercise's declared `assumptions` are asserted as constraints on that model,
    so the search only ever ranges over points the exercise admits. Without them the
    underspecified `(/ x 0)` made `x = 0` a "counterexample" to `x/x = 1` — a wrong
    grade on a correct answer. An untranslatable kind raises, and the query declines."""
    # Datatype + signatures from the exercise, mirroring ci.build_rule_source: an
    # `apply` must be routed by its declared signature, not by the legacy ℕ guess.
    dt = ci._parse_datatype(ex)
    definitions = ex.get("definitions") or []
    sigs = ci._signatures(definitions, dt)
    assumps = ci.parse_assumptions(ex)

    env: dict[str, str] = {}
    ci._infer(source, "Q", env, "", sigs, dt)
    ci._infer(target, "Q", env, "", sigs, dt)
    # Assumption terms are typed into the same environment, so a variable mentioned
    # only by an assumption is still declared in the emitted file.
    ci._infer_assumptions(assumps, env, "", sigs, dt)

    sort = ci._numsort(ex, ex.get("goal") or {"type": "eq"})
    ctx = ci._Ctx(sort, env, dt, sigs)

    nodes = [source, target] + [a["value"] for a in assumps]
    defs = ""
    if any(ci._mentions(n, ("pow",)) for n in nodes):
        defs += ci._build_pow(definitions, ctx)
    if any(ci._mentions(n, ("apply",)) for n in nodes):
        defs += ci._build_apply_defs(definitions, ctx)

    lhs = ci._term(source, ctx)
    rhs = ci._term(target, ctx)
    guards = ci._assumption_bools(assumps, ctx)

    n_vars = sorted(v for v, d in env.items() if d == "N")
    q_vars = sorted(v for v, d in env.items() if d == "Q")
    # A free variable of a non-ℕ datatype (a list, a tree) has no numeric reading, so a
    # `sat` here could only produce a constructor-term counterexample that
    # `_usable_witness` must reject anyway (D4). Decline the whole query instead of
    # emitting one whose only possible witness is unreportable — `unknown`, never a
    # partial witness attached to `proven_unequal`.
    if any(d not in ("N", "Q") for d in env.values()):
        raise _induction_error(
            f"{dt.name}-sorted variables are only supported in induction mode")
    # A ℕ-tagged variable is read back numerically as `(val n)`; `val` must exist even
    # if the body never coerced one (mirrors build_disprove_source's force_val).
    ctx.need_val = ctx.need_val or bool(n_vars)
    preamble = ci._preamble(ctx, defs)

    decls = [f"(declare-const {v} {sort})" for v in q_vars]
    decls += [f"(declare-const {v} Nat)" for v in n_vars]
    labels = q_vars + n_vars
    getvals = " ".join((f"(val {v})" if v in n_vars else v) for v in labels)
    body = (preamble + "\n".join(decls) + "\n"
            + "".join(f"(assert {g})\n" for g in guards)
            + f"(assert (not (= {lhs} {rhs})))\n"
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
    except ci.InductionError as e:
        return EquivResult("unknown", False, "untranslatable", detail=str(e))

    key = hashlib.sha256((prove_src + str(ci.REQUIRE_RECHECK)).encode()).hexdigest()
    if key in _CACHE:
        return _CACHE[key]
    if not cvc5_prover.cvc5_available():
        return EquivResult("unknown", False, "unavailable", detail="cvc5 toolchain unavailable")

    # 1) Disprove first — a numeric counterexample, when one exists. The witness gate
    #    is D4 *plus* the assumptions: a point the exercise excluded is not a
    #    counterexample, and one we cannot re-check against the declared assumptions
    #    degrades to `unknown` below rather than becoming a `proven_unequal`.
    dis = cvc5_prover.disprove(dis_src, labels)
    if dis.verdict == "sat" and ci.usable_witness(ex, dis.witness, labels):
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
        # Refuted, but the counterexample is unreportable (a datatype term, or a point
        # we cannot show the declared assumptions admit) — honest "unequal but no usable
        # witness" degrades to unknown, never a witness-less or assumption-violating
        # proven_unequal (protocol invariant).
        return _store(key, EquivResult("unknown", False, "rejected",
                                       detail="cvc5 refuted equivalence but produced no numeric "
                                              "witness admitted by the declared assumptions"))
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
