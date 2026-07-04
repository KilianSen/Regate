from __future__ import annotations

import copy
from dataclasses import dataclass


# ---------------------------------------------------------------------------
# MathNode JSON helpers (the persisted {type, value?, slots} shape).
# ---------------------------------------------------------------------------
def _num(v) -> dict:
    return {"type": "number", "value": str(v)}


def _flat_slots(node: dict) -> list[tuple[str, int]]:
    """(slot, index) pairs in alphabetical-then-positional order — the path encoding."""
    slots = node.get("slots") or {}
    order: list[tuple[str, int]] = []
    for key in sorted(slots):
        for i in range(len(slots[key])):
            order.append((key, i))
    return order


def _child(node: dict, idx: int) -> dict:
    key, i = _flat_slots(node)[idx]
    return node["slots"][key][i]


def at(node: dict, path) -> dict:
    for idx in path:
        node = _child(node, idx)
    return node


def replace(node: dict, path, new: dict) -> dict:
    if not path:
        return new
    idx, rest = path[0], path[1:]
    key, i = _flat_slots(node)[idx]
    out = copy.deepcopy(node)
    out["slots"][key][i] = replace(node["slots"][key][i], rest, new)
    return out


def match(pattern: dict, node: dict, env: dict | None = None) -> dict | None:
    """Structural match; a `wild` binds a subtree (same name ⇒ same subtree)."""
    env = {} if env is None else env
    if pattern["type"] == "wild":
        name = pattern["value"]
        if name in env:
            return env if env[name] == node else None
        env = dict(env)
        env[name] = node
        return env
    if pattern["type"] != node.get("type"):
        return None
    if pattern.get("value") != node.get("value"):
        return None
    ps, ns = pattern.get("slots") or {}, node.get("slots") or {}
    if sorted(ps) != sorted(ns):
        return None
    for key in sorted(ps):
        pl, nl = ps[key], ns[key]
        if len(pl) != len(nl):
            return None
        for pp, nn in zip(pl, nl):
            env = match(pp, nn, env)
            if env is None:
                return None
    return env


def instantiate(template: dict, env: dict) -> dict:
    if template["type"] == "wild":
        return copy.deepcopy(env[template["value"]])
    if "slots" not in template:
        out = {"type": template["type"]}
        if "value" in template:
            out["value"] = template["value"]
        return out
    return {"type": template["type"],
            "slots": {k: [instantiate(x, env) for x in v]
                      for k, v in template["slots"].items()}}


# ---------------------------------------------------------------------------
# A rule the Lean kernel has proven sound for THIS request.
# ---------------------------------------------------------------------------
# Leanregate has no built-in rule library: rules come from the API. Every rule is
# transmitted in `exercise.ruleset` and proven at request time by `lean_prover`
# (ring/field_simp + proof-carrying); a proven rule becomes a `ProvenRule` here
# via `proven_from_custom`. There is no static catalogue and no `Basic.lean` — a
# derivation can only be certified against rules the kernel has just proven.
@dataclass(frozen=True)
class ProvenRule:
    id: str
    lhs: dict
    rhs: dict
    lean: str            # the Lean theorem name that certified this rule at request time
    bidir: bool = False
    guarded: bool = False  # needs a ≠0 hypothesis Lean would demand; not auto-discharged


def proven_from_custom(rule: dict, lean: str) -> ProvenRule:
    """Build a `ProvenRule` from an inline custom rule that Lean has just proven
    at request time (see `lean_prover.prove_rule`). `lean` is the certifying
    theorem name. A rule carrying side conditions is `guarded`: its *conditional*
    identity is proven, but discharging the guard at a step still needs a declared
    assumption, so — as with the built-in fraction rules — the step-checker leaves
    it uncertifiable rather than guessing."""
    return ProvenRule(
        id=str(rule["id"]),
        lhs=rule["lhs"],
        rhs=rule["rhs"],
        lean=lean,
        bidir=bool(rule.get("bidirectional", False)),
        guarded=bool(rule.get("conditions")),
    )


# ---------------------------------------------------------------------------
# Step checking.
# ---------------------------------------------------------------------------
@dataclass(frozen=True)
class StepCheck:
    status: str          # "valid" | "invalid" | "uncertifiable"
    result: dict | None  # the state after the step, when structurally applicable
    reason: str
    lean: str | None = None


def check_step(state: dict, step: dict, rules: dict[str, ProvenRule] | None = None) -> StepCheck:
    """Check one derivation step against the rules the kernel proved for this
    request (`rules`; empty if none were transmitted/proven).

    "valid"          — an instance of a proven (unguarded) rule; result computed.
    "invalid"        — the rule does not apply at the path, or the claimed result
                       disagrees with the rule's output (a fabricated step).
    "uncertifiable"  — structurally fine but Lean would require a side condition,
                       or the rule has no proof; Leanregate will not grade it.
    """
    rules = rules or {}
    if step.get("kind", "A") == "B":
        return StepCheck("uncertifiable", None,
                         "Leibniz substitution (kind B) is not yet wired to a Lean proof")
    rid = step.get("rule")
    rule = rules.get(rid)
    if rule is None:
        return StepCheck("uncertifiable", None, f"no Lean proof for rule {rid!r}")
    reverse = step.get("direction") == "reverse"
    if reverse and not rule.bidir:
        return StepCheck("invalid", None, f"{rid} is forward-only; cannot apply in reverse")
    pattern, template = (rule.rhs, rule.lhs) if reverse else (rule.lhs, rule.rhs)
    path = tuple(step.get("path", []))
    try:
        sub = at(state, path)
    except (IndexError, KeyError):
        return StepCheck("invalid", None, f"path {list(path)} is not in the expression")
    env = match(pattern, sub, {})
    if env is None:
        return StepCheck("invalid", None, f"{rid} does not match at {list(path)}")
    if rule.guarded:
        return StepCheck("uncertifiable", None,
                         f"{rid} needs a ≠0 side condition Lean would require; cannot certify")
    result = replace(state, path, instantiate(template, env))
    claimed = step.get("result")
    if claimed is not None and claimed != result:
        return StepCheck("invalid", None, "claimed result does not match the rule output")
    return StepCheck("valid", result, "", lean=rule.lean)


@dataclass
class DerivationReport:
    status: str                  # "certified" | "invalid" | "uncertifiable"
    final: dict | None
    steps_out: list[dict]
    invalid_index: int | None = None
    reason: str = ""


def check_derivation(source: dict, steps: list[dict],
                     rules: dict[str, ProvenRule] | None = None) -> DerivationReport:
    """Replay a derivation, certifying each step against the rules proven for this
    request (`rules`; empty ⇒ every rule step is uncertifiable)."""
    state = source
    steps_out: list[dict] = []
    for i, step in enumerate(steps):
        res = check_step(state, step, rules)
        if res.status == "invalid":
            steps_out.append({"index": i, "status": "invalid", "reason": res.reason})
            return DerivationReport("invalid", None, steps_out, i, res.reason)
        if res.status == "uncertifiable":
            steps_out.append({"index": i, "status": "open", "reason": res.reason})
            return DerivationReport("uncertifiable", None, steps_out, i, res.reason)
        steps_out.append({"index": i, "status": "valid", "reason": f"Lean: {res.lean}"})
        state = res.result
    return DerivationReport("certified", state, steps_out)


# ---------------------------------------------------------------------------
# Induction: certify the STUDENT's base + inductive-step derivations.
# ---------------------------------------------------------------------------
# A proof by induction over `inductionVar` is graded like two ordinary
# derivations: the base case reduces P(0) to a tautology, and the inductive step
# reduces P(k+1) to a tautology while licensed to substitute the hypothesis P(k).
# The induction schema itself (Nat.rec) is sound, so two certified obligations
# certify ∀n.P(n). grade.py additionally runs lean_induction as a kernel backstop
# (it guards against inconsistent transmitted `definitions`). Crucially this reads
# the submission — an empty/garbage proof can no longer be auto-certified.
def substitute(node: dict, var: str, repl: dict) -> dict:
    """Replace every `variable var` in `node` with `repl` (structural)."""
    if node.get("type") == "variable" and str(node.get("value")) == var:
        return copy.deepcopy(repl)
    if "slots" not in node:
        return copy.deepcopy(node)
    out: dict = {"type": node["type"]}
    if "value" in node:
        out["value"] = node["value"]
    out["slots"] = {k: [substitute(c, var, repl) for c in v]
                    for k, v in node["slots"].items()}
    return out


def _is_reflexive(node: dict) -> bool:
    """True when `node` is an equality whose two sides are syntactically equal."""
    if node.get("type") != "eq":
        return False
    s = node["slots"]
    return s["left"][0] == s["right"][0]


def induction_rules(ex: dict, proven: dict[str, ProvenRule]) -> dict[str, ProvenRule]:
    """The kernel-proven inline rules (`proven`, from grade.py) plus the
    transmitted recursive `definitions` (pow_zero/…) as rewrite rules. The
    definitions are definitional equalities for the `def pw` the Lean backstop
    builds; that backstop re-proves the whole goal, so an inconsistent definition
    cannot yield a certified verdict."""
    rules = dict(proven)
    for d in (ex.get("definitions") or []):
        if d.get("id") and d.get("lhs") and d.get("rhs"):
            rules[str(d["id"])] = proven_from_custom(d, str(d["id"]))
    return rules


def _check_case(source: dict, steps: list[dict], rules: dict[str, ProvenRule],
                ih: tuple[dict, dict] | None) -> DerivationReport:
    """Replay one induction case. `ih=(lhs,rhs)` licenses a kind-B substitution
    by the inductive hypothesis (only in the step); the base passes ih=None."""
    state = source
    steps_out: list[dict] = []
    for i, step in enumerate(steps):
        if step.get("kind") == "B":
            if ih is None:
                r = "Leibniz substitution with no inductive hypothesis available"
                steps_out.append({"index": i, "status": "open", "reason": r})
                return DerivationReport("uncertifiable", None, steps_out, i, r)
            eqn = step.get("equation")
            if not (isinstance(eqn, list) and len(eqn) == 2
                    and eqn[0] == ih[0] and eqn[1] == ih[1]):
                r = "Leibniz substitution is not the inductive hypothesis"
                steps_out.append({"index": i, "status": "invalid", "reason": r})
                return DerivationReport("invalid", None, steps_out, i, r)
            path = tuple(step.get("path", []))
            try:
                target = at(state, path)
            except (IndexError, KeyError):
                r = f"path {list(path)} is not in the expression"
                steps_out.append({"index": i, "status": "invalid", "reason": r})
                return DerivationReport("invalid", None, steps_out, i, r)
            if target != ih[0]:
                r = "the substituted subterm is not the inductive hypothesis' LHS"
                steps_out.append({"index": i, "status": "invalid", "reason": r})
                return DerivationReport("invalid", None, steps_out, i, r)
            result = replace(state, path, copy.deepcopy(ih[1]))
            claimed = step.get("result")
            if claimed is not None and claimed != result:
                r = "claimed result does not match the inductive-hypothesis substitution"
                steps_out.append({"index": i, "status": "invalid", "reason": r})
                return DerivationReport("invalid", None, steps_out, i, r)
            steps_out.append({"index": i, "status": "valid", "reason": "inductive hypothesis"})
            state = result
            continue
        res = check_step(state, step, rules)
        if res.status == "invalid":
            steps_out.append({"index": i, "status": "invalid", "reason": res.reason})
            return DerivationReport("invalid", None, steps_out, i, res.reason)
        if res.status == "uncertifiable":
            steps_out.append({"index": i, "status": "open", "reason": res.reason})
            return DerivationReport("uncertifiable", None, steps_out, i, res.reason)
        steps_out.append({"index": i, "status": "valid", "reason": f"Lean: {res.lean}"})
        state = res.result
    return DerivationReport("certified", state, steps_out)


@dataclass
class InductionReport:
    status: str                  # "certified" | "invalid" | "uncertifiable"
    reason: str = ""
    base: DerivationReport | None = None
    step: DerivationReport | None = None


def check_induction(ex: dict, sub: dict,
                    proven: dict[str, ProvenRule] | None = None) -> InductionReport:
    """Certify the submitted base + inductive-step derivations for an induction
    exercise, using the kernel-proven inline rules (`proven`) + the transmitted
    definitions. Returns "invalid" (a wrong step or a missing obligation),
    "uncertifiable" (valid but unfinished / outside the proven fragment), or
    "certified" (both obligations reduce their goal to a tautology)."""
    goal = ex.get("goal")
    var = ex.get("inductionVar")
    if not goal or goal.get("type") != "eq" or not var:
        return InductionReport("uncertifiable",
                               "induction goal must be an equality with an inductionVar")
    var = str(var)
    base_steps = (sub.get("base") or {}).get("steps")
    step_steps = (sub.get("step") or {}).get("steps")
    if not base_steps or not step_steps:
        # No (complete) derivation was submitted — the student has not *attempted*
        # the obligations. That is not the same as a *wrong* proof: an absent
        # derivation must never be scored `invalid_derivation`/0 (a false zero on a
        # possibly-true theorem). Report it as uncertifiable so grade.py routes it
        # to `unknown` (route to review), honoring "never a false grade".
        return InductionReport("uncertifiable",
                               "no induction derivation submitted: both a base-case and an "
                               "inductive-step derivation are required to grade the proof")

    rules = induction_rules(ex, proven or {})
    base_goal = substitute(goal, var, _num(0))
    succ = {"type": "succ", "slots": {"inner": [{"type": "variable", "value": var}]}}
    step_goal = substitute(goal, var, succ)
    ih = (goal["slots"]["left"][0], goal["slots"]["right"][0])  # P(var)

    base = _check_case(base_goal, base_steps, rules, ih=None)
    if base.status != "certified":
        return InductionReport(base.status, f"base case: {base.reason}", base=base)
    if not _is_reflexive(base.final):
        return InductionReport("uncertifiable",
                               "base case did not reduce both sides to a common form", base=base)

    step = _check_case(step_goal, step_steps, rules, ih=ih)
    if step.status != "certified":
        return InductionReport(step.status, f"inductive step: {step.reason}", base=base, step=step)
    if not _is_reflexive(step.final):
        return InductionReport("uncertifiable",
                               "inductive step did not reduce both sides to a common form",
                               base=base, step=step)
    return InductionReport("certified",
                           "base case and inductive step both certified", base=base, step=step)
