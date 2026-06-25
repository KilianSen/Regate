"""Robust equivalence decision + proof re-checking (the soundness/fairness layer).

Collapsing "is the student's answer equivalent to the goal?" into a single
boolean is where both failure modes hide:

  * a false **positive** (unsound credit) if we trust an un-recertified proof or
    a bare oracle ``check``;
  * a false **negative** (unfair zero) if we read an ambiguous "no proof within
    budget" as "wrong".

``decide_equivalence`` returns one of four honest outcomes instead:

  PROVEN_EQUAL          -- a constructive, re-checked proof exists (certificate)
  PROVEN_UNEQUAL        -- a numeric counterexample exists (sound disproof)
  EQUAL_NO_CERTIFICATE  -- the oracle says equal but no proof was reconstructed
                           (suspicious; do not auto-grade as correct)
  UNKNOWN               -- neither proof nor disproof within budget (escalate /
                           review; never silently a zero)

Order matters: we try to **disprove first** (numbers are ground truth and cheap),
then to **prove with a re-checked certificate**, then fall back to the weaker
oracle.  Every PROVEN_EQUAL is independently re-validated step-by-step by
``recheck_proof`` -- the trusted kernel -- so the proof backends never have the
last word on soundness.
"""
from __future__ import annotations

from dataclasses import dataclass

from .backend import equivalent
from .catalogue import BY_ID, CATALOGUE, Rule
from .conditions import DISCHARGED, discharge
from .hints import shortest_path
from .matching import instantiate, match
from .model import MathNode, Path
from .proof_egraph import egg_prove
from .semantics import find_counterexample

PROVEN_EQUAL = "proven_equal"
PROVEN_UNEQUAL = "proven_unequal"
EQUAL_NO_CERTIFICATE = "equal_no_certificate"
UNKNOWN = "unknown"


# ---------------------------------------------------------------------------
# Trusted kernel: independently re-validate a proof's steps.
# ---------------------------------------------------------------------------
def _apply_equality(state: MathNode, rule: Rule, path: Path, forward: bool):
    """Re-derive one step as an equality move; ``None`` if it isn't legitimate."""
    pattern, template = (rule.lhs, rule.rhs) if forward else (rule.rhs, rule.lhs)
    try:
        sub = state.at(path)
    except (IndexError, ValueError):
        return None
    env = match(pattern, sub)
    if env is None:
        return None
    # guards must be (literal-)discharged for the equality to hold
    if not all(discharge(c, env[c.var]) == DISCHARGED for c in rule.conditions):
        return None
    try:
        new_sub = instantiate(template, env)
    except KeyError:               # template wildcard not bound -> not a real step
        return None
    return state.replace(path, new_sub)


def recheck_proof(source: MathNode, steps, rules: list[Rule] | None = None) -> bool:
    """Independently confirm each step is a real, guarded rule application.

    Works for both backends' steps (BFS ``Step`` and egg ``ProofStep``); the egg
    direction flag, when present, is honoured but either direction is accepted so
    long as it reproduces the claimed line.  ``rules`` scopes the id lookup to the
    request's ruleset (custom or built-in); defaults to the shipped catalogue.
    """
    by_id = BY_ID if rules is None else {r.id: r for r in rules}
    state = source
    for st in steps:
        rule = by_id.get(st.rule_id)
        if rule is None:
            return False
        forward = getattr(st, "forward", True)
        nxt = _apply_equality(state, rule, st.path, forward)
        if nxt is None or nxt != st.state:
            nxt = _apply_equality(state, rule, st.path, not forward)
            if nxt is None or nxt != st.state:
                return False
        state = nxt
    return True


# ---------------------------------------------------------------------------
# Three-valued decision.
# ---------------------------------------------------------------------------
@dataclass
class Verdict:
    outcome: str
    backend: str | None = None
    proof: list | None = None              # certificate, if PROVEN_EQUAL
    witness: dict | None = None            # counterexample, if PROVEN_UNEQUAL

    @property
    def certified_equal(self) -> bool:
        return self.outcome == PROVEN_EQUAL


def decide_equivalence(a: MathNode, b: MathNode, rules: list[Rule] | None = None, *,
                       disprove_trials: int = 400,
                       bounds: tuple[int, ...] = (5, 8, 12),
                       max_depth: int = 8) -> Verdict:
    rules = CATALOGUE if rules is None else rules

    # 1) sound disproof first (ground truth, cheap)
    ce = find_counterexample(a, b, disprove_trials)
    if ce is not None:
        return Verdict(PROVEN_UNEQUAL, backend="semantics", witness=ce)

    # 2) constructive, re-checked proof -- egg (escalating bound), then BFS.
    #    NB: an empty proof ([]) is a *valid* certificate (already equal), so
    #    test `is not None`, not truthiness.
    for bound in bounds:
        proof = egg_prove(a, b, rules, bound=bound)
        if proof is not None and recheck_proof(a, proof, rules):
            return Verdict(PROVEN_EQUAL, backend="egg", proof=proof)
    path = shortest_path(a, b, rules, max_depth=max_depth)
    if path is not None and recheck_proof(a, path, rules):
        return Verdict(PROVEN_EQUAL, backend="bfs", proof=path)

    # 3) weaker oracle evidence (no reconstructed certificate)
    if equivalent(a, b, rules=rules):
        return Verdict(EQUAL_NO_CERTIFICATE, backend="oracle")

    # 4) honestly unknown
    return Verdict(UNKNOWN)


def grade_robust(student_final: MathNode, target: MathNode,
                 rules: list[Rule] | None = None) -> tuple[int | None, Verdict]:
    """Grade with explicit handling of the ambiguous case.

    Returns ``(score, verdict)``.  ``score`` is ``None`` for UNKNOWN /
    EQUAL_NO_CERTIFICATE -- meaning "do not auto-grade; escalate to review" --
    rather than a false zero or unearned full marks.
    """
    v = decide_equivalence(student_final, target, rules)
    if v.outcome == PROVEN_EQUAL:
        return 100, v
    if v.outcome == PROVEN_UNEQUAL:
        return 0, v
    return None, v        # EQUAL_NO_CERTIFICATE or UNKNOWN -> needs review
