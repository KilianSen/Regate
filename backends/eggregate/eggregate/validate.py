"""Step-local verification.

The key point: a step produced by *matching a rule's LHS and
emitting its RHS* is valid **by construction** -- you do not need an e-graph to
re-confirm an equality you just generated.  Soundness therefore lives in this
validator plus the guarded rule library, not in per-step saturation.  The
e-graph is reserved for what this layer cannot certify cheaply: manual edits and
macro-steps (see ``backend.equivalent`` / the macro-step checker).

Two interactions, kept strictly separate:

  * Type A -- structural rewrite: apply a catalogue rule at a path.
  * Type B -- contextual (Leibniz/congruence) substitution: replace an
    occurrence of a previously-established equality's LHS with its RHS.

Each returns a three-valued ``StepResult`` (valid / open / invalid), mirroring
the three-valued discharge of side conditions: "open" means the rewrite is
structurally fine but a guard still needs the student to discharge it.
"""
from __future__ import annotations

from dataclasses import dataclass, field

from .rule import Rule
from .conditions import DISCHARGED, OPEN, VIOLATED, Assumption, SideCondition, discharge
from .matching import instantiate, match
from .model import MathNode, Path, pretty

VALID = "valid"
INVALID = "invalid"
# (OPEN is imported from conditions)


@dataclass(frozen=True)
class StepResult:
    status: str                       # VALID | OPEN | INVALID
    result: MathNode | None = None    # resulting line, if structurally applicable
    reason: str = ""
    open_conditions: tuple[SideCondition, ...] = ()

    @property
    def ok(self) -> bool:
        return self.status == VALID


# ---------------------------------------------------------------------------
# Type A -- structural rewrite (rule application).
# ---------------------------------------------------------------------------
def apply_rule(state: MathNode, rule: Rule, path: Path, *, reverse: bool = False,
               assumptions: frozenset[Assumption] = frozenset()) -> StepResult:
    """Validate and perform one rule application at ``path``.

    Returns the resulting line and whether the step is valid by construction,
    blocked by a violated guard, or pending a guard the student must discharge.
    """
    if reverse and not rule.bidir:
        return StepResult(INVALID, reason=f"{rule.id} is forward-only; cannot apply in reverse")

    pattern, template = (rule.rhs, rule.lhs) if reverse else (rule.lhs, rule.rhs)
    try:
        sub = state.at(path)
    except (IndexError, ValueError):
        return StepResult(INVALID, reason=f"path {list(path)} is not in the expression")

    env = match(pattern, sub)
    if env is None:
        return StepResult(INVALID,
                          reason=f"{rule.id} does not match {pretty(sub)} at {list(path)}")

    # Discharge guards against the bindings and the student's assumptions. A guard
    # on a wildcard the *pattern* does not bind cannot be decided at all -- that
    # happens when a guarded rule is run in the direction whose pattern drops the
    # guarded variable (reverse `a/a -> 1`: the `1` says nothing about `a`).
    # Applying it would silently invent a witness for the guard, so refuse.
    open_conds, violated = [], []
    for cond in rule.conditions:
        binding = env.get(cond.var)
        if binding is None:
            side = "rhs" if reverse else "lhs"
            return StepResult(
                INVALID,
                reason=f"{rule.id} cannot be applied "
                       f"{'in reverse' if reverse else 'forward'}: its side condition on "
                       f"'{cond.var}' is undecidable because the {side} pattern does not "
                       f"bind '{cond.var}'")
        verdict = discharge(cond, binding, assumptions)
        if verdict == VIOLATED:
            violated.append(cond)
        elif verdict == OPEN:
            open_conds.append(cond)
    if violated:
        return StepResult(INVALID,
                          reason="side condition violated: "
                                 + ", ".join(c.describe(env[c.var]) for c in violated))

    result = state.replace(path, instantiate(template, env))
    if open_conds:
        return StepResult(OPEN, result=result,
                          reason="needs assumption: "
                                 + ", ".join(c.describe(env[c.var]) for c in open_conds),
                          open_conditions=tuple(open_conds))
    return StepResult(VALID, result=result)


# ---------------------------------------------------------------------------
# Type B -- contextual substitution (Leibniz / congruence).
# ---------------------------------------------------------------------------
@dataclass(frozen=True)
class Equation:
    """An established equality available for reuse (a proven earlier line)."""

    lhs: MathNode
    rhs: MathNode

    def __str__(self) -> str:
        return f"{pretty(self.lhs)} = {pretty(self.rhs)}"


def apply_equation(state: MathNode, equation: Equation, path: Path, *,
                   in_scope: bool = True) -> StepResult:
    """Replace the occurrence at ``path`` of ``equation.lhs`` with ``equation.rhs``.

    Validity (Type B): the equation is in scope AND the targeted
    subtree equals the equation's LHS exactly (structural equality; the model has
    no binders, so no alpha-equivalence is needed).
    """
    if not in_scope:
        return StepResult(INVALID, reason=f"equation '{equation}' is not in scope here")
    try:
        sub = state.at(path)
    except (IndexError, ValueError):
        return StepResult(INVALID, reason=f"path {list(path)} is not in the expression")
    if sub != equation.lhs:
        return StepResult(
            INVALID,
            reason=f"occurrence {pretty(sub)} at {list(path)} is not the equation's LHS "
                   f"{pretty(equation.lhs)}")
    return StepResult(VALID, result=state.replace(path, equation.rhs))


# ---------------------------------------------------------------------------
# Whole-proof verification.
# ---------------------------------------------------------------------------
@dataclass(frozen=True)
class Move:
    """A claimed derivation step, tagged by interaction kind."""

    kind: str                       # 'A' (rule) | 'B' (equation)
    path: Path
    rule: Rule | None = None
    reverse: bool = False
    equation: Equation | None = None
    in_scope: bool = True


@dataclass
class ChainReport:
    valid: bool
    reached_goal: bool
    states: list[MathNode] = field(default_factory=list)
    results: list[StepResult] = field(default_factory=list)

    @property
    def score(self) -> int:
        return 100 if (self.valid and self.reached_goal) else 0


def verify_chain(source: MathNode, moves: list[Move], goal: MathNode, *,
                 assumptions: frozenset[Assumption] = frozenset()) -> ChainReport:
    """Replay a derivation, checking every step is locally valid.

    With a sound step chain, endpoint equivalence follows by transitivity, so the
    real work is the per-step invariant -- this never invokes the e-graph.  OPEN
    steps (undischarged guards) are treated as not-yet-valid for the chain.
    """
    report = ChainReport(valid=True, reached_goal=False, states=[source])
    state = source
    for move in moves:
        if move.kind == "A":
            res = apply_rule(state, move.rule, move.path,
                             reverse=move.reverse, assumptions=assumptions)
        elif move.kind == "B":
            res = apply_equation(state, move.equation, move.path, in_scope=move.in_scope)
        else:
            res = StepResult(INVALID, reason=f"unknown move kind {move.kind!r}")
        report.results.append(res)
        if not res.ok:
            report.valid = False
            break
        state = res.result
        report.states.append(state)
    report.reached_goal = report.valid and state == goal
    return report
