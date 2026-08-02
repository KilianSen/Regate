from __future__ import annotations

import copy
import json
from dataclasses import dataclass

# Strict symbolic checking of a student's derivation steps: each Type-A step must
# be an *instance of the claimed rule at the claimed path* producing exactly the
# claimed result; each Type-B step must substitute exactly the inductive
# hypothesis. No value-equivalence leniency — a step that reaches a value-equal
# state by any other means than the claimed rule is rejected. With AC enabled
# (`exercise.options.ac_normalization`), `add`/`mul` are matched and compared
# modulo associativity + commutativity. The rules come from the request
# (`exercise.ruleset` + `exercise.definitions`); their *soundness* is backstopped
# by the cvc5 kernel certifying the goal in cvc5_induction. stdlib-only; the matcher
# mirrors the protocol's alphabetical-slot path encoding.

AC_OPS_DEFAULT = ("add", "mul")


# ---------------------------------------------------------------------------
# MathNode helpers + path encoding (the {type, value?, slots} shape).
# ---------------------------------------------------------------------------
def _flat_slots(node: dict) -> list[tuple[str, int]]:
    """(slot, index) pairs in alphabetical-then-positional order — the path encoding."""
    slots = node.get("slots") or {}
    order: list[tuple[str, int]] = []
    for key in sorted(slots):
        for i in range(len(slots[key])):
            order.append((key, i))
    return order


def at(node: dict, path) -> dict:
    for idx in path:
        key, i = _flat_slots(node)[idx]
        node = node["slots"][key][i]
    return node


def replace(node: dict, path, new: dict) -> dict:
    if not path:
        return new
    idx, rest = path[0], path[1:]
    key, i = _flat_slots(node)[idx]
    out = copy.deepcopy(node)
    out["slots"][key][i] = replace(node["slots"][key][i], rest, new)
    return out


def instantiate(template: dict, env: dict) -> dict:
    if template["type"] == "wild":
        return copy.deepcopy(env[template["value"]])
    out = {"type": template["type"]}
    if "value" in template:                       # e.g. an `apply` carries the fn name
        out["value"] = template["value"]
    if "slots" in template:
        out["slots"] = {k: [instantiate(x, env) for x in v]
                        for k, v in template["slots"].items()}
    return out


def substitute(node: dict, var: str, repl: dict) -> dict:
    """Replace every `variable var` in `node` with `repl`."""
    if node.get("type") == "variable" and str(node.get("value")) == var:
        return copy.deepcopy(repl)
    out = copy.deepcopy(node)
    for kids in (out.get("slots") or {}).values():
        for i, ch in enumerate(kids):
            kids[i] = substitute(ch, var, repl)
    return out


def generalize_ih(node: dict, indvar: str) -> dict:
    """Turn every `variable` except the induction variable into a `wild` of the same
    name. The inductive hypothesis is universal in its accumulators (cvc5 co-quantifies
    them in build_prove_source), so in the step the student may apply it at a *shifted*
    accumulator — `_match` recovers that instance. The induction variable stays literal:
    the IH holds at `n`, not at an arbitrary value."""
    if node.get("type") == "variable" and str(node.get("value")) != indvar:
        return {"type": "wild", "value": node["value"]}
    out = {"type": node.get("type")}
    if "value" in node:
        out["value"] = node["value"]
    if "slots" in node:
        out["slots"] = {k: [generalize_ih(c, indvar) for c in v]
                        for k, v in node["slots"].items()}
    return out


def _wild_names(node: dict) -> set:
    """Every `wild` name appearing in a template."""
    names = {node["value"]} if node.get("type") == "wild" else set()
    for kids in (node.get("slots") or {}).values():
        for k in kids:
            names |= _wild_names(k)
    return names


# ---------------------------------------------------------------------------
# AC (associativity + commutativity) canonicalisation and matching.
# ---------------------------------------------------------------------------
def _operands(node: dict, op: str) -> list[dict]:
    """Flatten an AC operator into its operand list (assoc): a+(b+c) -> [a,b,c]."""
    if node.get("type") != op:
        return [node]
    s = node["slots"]
    return _operands(s["left"][0], op) + _operands(s["right"][0], op)


def _combine(ops: list[dict], op: str) -> dict:
    """Rebuild a right-associated `op` tree from operands (≥1)."""
    acc = ops[-1]
    for o in reversed(ops[:-1]):
        acc = {"type": op, "slots": {"left": [o], "right": [acc]}}
    return acc


def ac_normalize(node: dict, ac: tuple = AC_OPS_DEFAULT) -> dict:
    """Canonical form: flatten AC ops, normalise + sort operands (comm), rebuild."""
    t = node.get("type")
    if "slots" not in node:
        out = {"type": t}
        if "value" in node:
            out["value"] = node["value"]
        return out
    if t in ac:
        ops = sorted((ac_normalize(o, ac) for o in _operands(node, t)),
                     key=lambda n: json.dumps(n, sort_keys=True))
        return _combine(ops, t)
    out = {"type": t}
    if "value" in node:
        out["value"] = node["value"]
    out["slots"] = {k: [ac_normalize(c, ac) for c in v] for k, v in node["slots"].items()}
    return out


def ac_equal(a: dict, b: dict, ac: tuple) -> bool:
    return a == b if not ac else ac_normalize(a, ac) == ac_normalize(b, ac)


def _assign(concrete: list[dict], node_ops: list[dict], env: dict, ac: tuple):
    """Match each concrete pattern operand to a distinct node operand
    (backtracking). Returns (env, leftover_ops) or None."""
    if not concrete:
        return env, node_ops
    cp = concrete[0]
    for i, no in enumerate(node_ops):
        e = _match(cp, no, env, ac)
        if e is not None:
            res = _assign(concrete[1:], node_ops[:i] + node_ops[i + 1:], e, ac)
            if res is not None:
                return res
    return None


def _match(pattern: dict, node: dict, env: dict | None, ac: tuple) -> dict | None:
    """Structural match (AC-aware when `ac` is non-empty). A `wild` binds a subtree
    (same name ⇒ AC-equal subtree). `ac=()` ⇒ exact structural matching."""
    env = {} if env is None else env
    if pattern["type"] == "wild":
        name = pattern["value"]
        if name in env:
            return env if ac_equal(env[name], node, ac) else None
        env = dict(env)
        env[name] = node
        return env
    pt = pattern["type"]
    if pt in ac and node.get("type") == pt:
        pat_ops = _operands(pattern, pt)
        node_ops = _operands(node, pt)
        concrete = [p for p in pat_ops if p.get("type") != "wild"]
        wilds = [p for p in pat_ops if p.get("type") == "wild"]
        res = _assign(concrete, list(node_ops), env, ac)
        if res is None:
            return None
        env2, leftover = res
        if not wilds:
            return env2 if not leftover else None
        if len(leftover) < len(wilds):
            return None
        # First wilds bind one operand each; the last binds the AC-combine of the rest.
        leftover = list(leftover)
        for w in wilds[:-1]:
            env2 = _match(w, leftover.pop(0), env2, ac)
            if env2 is None:
                return None
        return _match(wilds[-1], _combine(leftover, pt), env2, ac)
    if pt != node.get("type") or pattern.get("value") != node.get("value"):
        return None
    ps, ns = pattern.get("slots") or {}, node.get("slots") or {}
    if sorted(ps) != sorted(ns):
        return None
    for key in sorted(ps):
        pl, nl = ps[key], ns[key]
        if len(pl) != len(nl):
            return None
        for pp, nn in zip(pl, nl):
            env = _match(pp, nn, env, ac)
            if env is None:
                return None
    return env


def is_reflexive(node: dict, ac: tuple = ()) -> bool:
    s = node.get("slots") or {}
    return node.get("type") == "eq" and bool(s.get("left") and s.get("right")) \
        and ac_equal(s["left"][0], s["right"][0], ac)


# ---------------------------------------------------------------------------
# Rules transmitted in the request (no built-in catalogue).
# ---------------------------------------------------------------------------
@dataclass(frozen=True)
class Rule:
    id: str
    lhs: dict
    rhs: dict
    bidir: bool = False
    guarded: bool = False
    # Has cvc5 proven this rule for *this request*? Transmitted rules are untrusted
    # exercise data: applying one correctly proves nothing if the rule itself is
    # false. Recursive `definitions` are definitional, hence trusted.
    proven: bool = False


def build_rules(ex: dict, proven_ids: set[str]) -> dict[str, Rule]:
    """`exercise.ruleset` (transmitted rules, inline) + `exercise.definitions`
    (recursive defs) as a single id→Rule table for matching.

    ``proven_ids`` are the ruleset ids cvc5 proved for this request; a rule outside
    that set is present (so we can name it) but not usable to certify.
    """
    rules: dict[str, Rule] = {}
    for src in ex.get("ruleset") or []:
        rid, lhs, rhs = src.get("id"), src.get("lhs"), src.get("rhs")
        if rid and lhs and rhs:
            rules[str(rid)] = Rule(str(rid), lhs, rhs,
                                   bool(src.get("bidirectional")), bool(src.get("conditions")),
                                   proven=str(rid) in proven_ids)
    for src in ex.get("definitions") or []:
        rid, lhs, rhs = src.get("id"), src.get("lhs"), src.get("rhs")
        if rid and lhs and rhs:
            rules[str(rid)] = Rule(str(rid), lhs, rhs,
                                   bool(src.get("bidirectional")), bool(src.get("conditions")),
                                   proven=True)
    return rules


def ac_ops(ex: dict) -> tuple:
    """The AC operator set for this exercise — () unless ac_normalization is on."""
    opts = ex.get("options") or {}
    return AC_OPS_DEFAULT if opts.get("ac_normalization") else ()


# ---------------------------------------------------------------------------
# Replaying one induction obligation (base or step) strictly.
# ---------------------------------------------------------------------------
@dataclass
class CaseReport:
    status: str          # "certified" | "invalid" | "uncertifiable"
    final: dict | None
    reason: str = ""


def _check_step(state: dict, step: dict, rules: dict[str, Rule], ac: tuple) -> tuple[str, dict | None, str]:
    rid = step.get("rule")
    rule = rules.get(rid)
    if rule is None:
        return ("uncertifiable", None, f"unknown rule {rid!r} (not in the transmitted ruleset/definitions)")
    if not rule.proven:
        # Correctly applying a false rule proves nothing. cvc5 certifies the *goal*,
        # not the ruleset, so an unproven rule can never be composed into a certified
        # verdict — it is honestly inconclusive, not a wrong answer.
        # (Only reachable under `options.verify_rules`; otherwise rules are trusted.)
        return ("uncertifiable", None,
                f"{rid} was not proven by cvc5 under options.verify_rules; a step "
                f"citing an unproven rule cannot be certified")
    reverse = step.get("direction") == "reverse"
    if reverse and not rule.bidir:
        return ("invalid", None, f"{rid} is forward-only; cannot apply in reverse")
    pattern, template = (rule.rhs, rule.lhs) if reverse else (rule.lhs, rule.rhs)
    path = tuple(step.get("path", []))
    try:
        sub = at(state, path)
    except (IndexError, KeyError, TypeError):
        return ("invalid", None, f"path {list(path)} is not in the expression")
    env = _match(pattern, sub, {}, ac)
    if env is None:
        return ("invalid", None, f"{rid} does not match at {list(path)}")
    if rule.guarded:
        return ("uncertifiable", None, f"{rid} needs a side condition that cannot be discharged here")
    result = replace(state, path, instantiate(template, env))
    claimed = step.get("result")
    if claimed is not None and not ac_equal(claimed, result, ac):
        return ("invalid", None, f"claimed result does not match applying {rid} at {list(path)}")
    # Chain the student's claimed state (AC-equal to the computed result) so later
    # steps' paths align with the tree the student is editing.
    return ("valid", claimed if claimed is not None else result, "")


def check_case(source: dict, steps: list[dict], rules: dict[str, Rule],
               ih, ac: tuple = ()) -> CaseReport:
    """Replay one obligation. `ih` licenses a kind-B substitution by an inductive
    hypothesis (step only); the base passes ih=None. `ih` is None, a single
    `(lhs, rhs)` tuple, or a **list** of them — a binary tree's step has one IH per
    recursive child (`P(l)`, `P(r)`), and a kind-B step may apply any of them."""
    if ih is None:
        ihs: list = []
    elif isinstance(ih, tuple):
        ihs = [ih]
    else:
        ihs = list(ih)
    state = source
    for i, step in enumerate(steps):
        if step.get("kind") == "B":
            if not ihs:
                return CaseReport("uncertifiable", None, f"step {i}: IH substitution with no hypothesis available")
            path = tuple(step.get("path", []))
            try:
                target = at(state, path)
            except (IndexError, KeyError, TypeError):
                return CaseReport("invalid", None, f"step {i}: path {list(path)} is not in the expression")
            # Each IH is generalized over its accumulators (wildcarded by
            # grade_derivation). Recover the instance σ the student applies by matching
            # one side of an IH against the target subterm; a pure-ℕ IH has no wildcards,
            # so this reduces to the old exact match. Try every available IH and accept
            # the first whose instance equals the student's declared `equation` — a tree
            # step applies P(l) then P(r) at different subterms. Sound because cvc5
            # certifies the *co-quantified* goal, the same universal each IH claims.
            eqn = step.get("equation")
            if not (isinstance(eqn, list) and len(eqn) == 2):
                return CaseReport("invalid", None, f"step {i}: kind-B step needs an [lhs, rhs] equation")
            # An IH is an *equation*, so it licenses a substitution in either direction: forward
            # rewrites `P.lhs·σ` to `P.rhs·σ`, reverse folds `P.rhs·σ` back into `P.lhs·σ`. Both are
            # instances of the same co-quantified universal cvc5 certifies, so admitting the reverse
            # adds no proving strength — it only lets a derivation *introduce* a recursive call
            # (fold `nodes l + nodes r` into `aux r (nodes l)`), which accumulator proofs need and
            # which the forward-only matcher made unreachable. The declared `equation` is always
            # (pre-rewrite, post-rewrite), so it pins the direction taken and is re-checked below;
            # forward is tried first, leaving every previously accepted derivation accepted.
            replacement = None
            for h in ihs:
                for pattern, template in ((h[0], h[1]), (h[1], h[0])):
                    sigma = _match(pattern, target, {}, ac)
                    if sigma is None or not _wild_names(template) <= set(sigma):
                        continue
                    cand_from, cand_to = instantiate(pattern, sigma), instantiate(template, sigma)
                    if ac_equal(eqn[0], cand_from, ac) and ac_equal(eqn[1], cand_to, ac):
                        replacement = cand_to
                        break
                if replacement is not None:
                    break
            if replacement is None:
                return CaseReport("invalid", None,
                                  f"step {i}: substitution is not an instance of the inductive hypothesis")
            result = replace(state, path, copy.deepcopy(replacement))
            claimed = step.get("result")
            if claimed is not None and not ac_equal(claimed, result, ac):
                return CaseReport("invalid", None, f"step {i}: claimed result does not match the IH substitution")
            state = claimed if claimed is not None else result
            continue
        status, result, reason = _check_step(state, step, rules, ac)
        if status != "valid":
            return CaseReport(status, None, f"step {i}: {reason}")
        state = result
    return CaseReport("certified", state)


# ---------------------------------------------------------------------------
# Grading an ordinary (non-induction) transformation/equation derivation.
# Same strict per-step semantics as check_case, but it reports every step's status
# in the protocol's StepStatus shape and stops at the first non-valid step. A
# kind-B (Leibniz) step has no inductive hypothesis to license it here, so it is
# `open` (uncertifiable) — the caller falls back to the SMT equivalence oracle on
# the endpoint rather than certifying the substitution symbolically.
# ---------------------------------------------------------------------------
@dataclass
class DerivationReport:
    status: str                 # "valid" | "invalid" | "uncertifiable"
    steps_out: list            # [{"index", "status", "reason"}]
    final: dict | None
    invalid_index: int | None = None
    reason: str = ""


def check_derivation(source: dict, steps: list[dict], rules: dict[str, Rule],
                     ac: tuple = ()) -> DerivationReport:
    state = source
    steps_out: list[dict] = []
    for i, step in enumerate(steps):
        if step.get("kind") == "B":
            steps_out.append({"index": i, "status": "open",
                              "reason": "Leibniz substitution is not symbolically certified by "
                                        "cvc5regate; endpoint equivalence is checked by the solver"})
            return DerivationReport("uncertifiable", steps_out, None, i,
                                    steps_out[-1]["reason"])
        status, result, reason = _check_step(state, step, rules, ac)
        if status == "valid":
            steps_out.append({"index": i, "status": "valid", "reason": ""})
            state = result
            continue
        # "invalid" (wrong rule/path/result) vs "uncertifiable" (unknown/unproven/guarded
        # rule) — the protocol StepStatus is `invalid` or `open` respectively.
        steps_out.append({"index": i, "status": "invalid" if status == "invalid" else "open",
                          "reason": reason})
        return DerivationReport(status, steps_out, None, i, reason)
    return DerivationReport("valid", steps_out, state)
