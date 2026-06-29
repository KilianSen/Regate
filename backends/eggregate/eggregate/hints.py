"""The directed step engine and hint generation (thesis Section 5.6 / B.4).

This interprets the *same* catalogue (``catalogue.py``) as directed tree
rewrites -- the step-by-step engine that mirrors the MS1 kernel.  On top of it:

  * ``greedy_hints`` reproduces ``suggestHints``: enumerate every (path, rule)
    rewrite that changes the tree, dedup, rank by one-ply distance to the goal,
    return the best three (Table 8).  This is the heuristic the thesis critiques.

  * ``shortest_path`` is the MS3 improvement (Section B.4): a breadth-first
    search over directed applications that returns a *whole* path to the goal,
    so guidance can be ranked by progress-to-goal rather than a single greedy
    next move -- and can surface a pedagogically natural ordering.
"""
from __future__ import annotations

from collections import deque
from dataclasses import dataclass

from .catalogue import Rule
from .conditions import DISCHARGED, discharge
from .matching import instantiate, match
from .model import MathNode, Path, distance, pretty


def _constraint_ok(rule: Rule, env: dict[str, MathNode]) -> bool:
    """A rule may be auto-applied during search only if every guard is
    DISCHARGED purely from the literals present (search carries no assumptions)."""
    return all(discharge(c, env[c.var]) == DISCHARGED for c in rule.conditions)


@dataclass(frozen=True)
class Application:
    """One directed rewrite that changes the tree."""

    rule_id: str
    path: Path
    result: MathNode
    forward: bool = True       # False = a bidirectional rule applied right-to-left


def _reversible(rules: list[Rule]) -> list[Rule]:
    """Bidirectional rules safe to also search backward (rhs->lhs) — guard-free and
    neither side a lone wildcard, so the reverse pattern is bound and terminating.
    Mirrors ``proof_egraph.directed_rules`` exactly (e.g. excludes ``neg_neg``)."""
    return [r for r in rules
            if r.bidir and not r.conditions and r.lhs.op != "wild" and r.rhs.op != "wild"]


def applications(node: MathNode, rules: list[Rule], *, bidirectional: bool = False) -> list[Application]:
    """Every (rule, path) application that changes ``node``, deduped.

    Forward only by default (the directed step engine / hint semantics). With
    ``bidirectional=True`` it also emits the right-to-left direction of every
    safely-reversible rule — used only by the proof-certificate search, where each
    step is independently re-checked by ``robust.recheck_proof``."""
    out: list[Application] = []
    seen: set[tuple[str, bool, MathNode]] = set()

    def emit(rule_id, pattern, template, forward):
        for path in node.paths():
            sub = node.at(path)
            env = match(pattern, sub)
            if env is None:
                continue
            try:
                new_sub = instantiate(template, env)
            except KeyError:           # template wildcard unbound -> not a real step
                continue
            if new_sub == sub:
                continue
            result = node.replace(path, new_sub)
            key = (rule_id, forward, result)
            if key in seen:
                continue
            seen.add(key)
            out.append(Application(rule_id, path, result, forward))

    for rule in rules:
        # forward direction must still discharge guards from the literals present
        for path in node.paths():
            sub = node.at(path)
            env = match(rule.lhs, sub)
            if env is None or not _constraint_ok(rule, env):
                continue
            new_sub = instantiate(rule.rhs, env)
            if new_sub == sub:
                continue
            result = node.replace(path, new_sub)
            key = (rule.id, True, result)
            if key in seen:
                continue
            seen.add(key)
            out.append(Application(rule.id, path, result, True))
    if bidirectional:
        for rule in _reversible(rules):
            emit(rule.id, rule.rhs, rule.lhs, False)
    return out


# ---------------------------------------------------------------------------
# Greedy one-ply hints (reproduces Table 8 -- the heuristic MS3 improves on).
# ---------------------------------------------------------------------------
def greedy_hints(state: MathNode, target: MathNode, rules: list[Rule], k: int = 3):
    apps = applications(state, rules)
    ranked = sorted(apps, key=lambda a: (distance(a.result, target), a.rule_id))
    return ranked[:k]


# ---------------------------------------------------------------------------
# Multi-step hint: a whole path to the goal (the MS3 improvement, Section B.4).
# ---------------------------------------------------------------------------
@dataclass(frozen=True)
class Step:
    rule_id: str
    path: Path
    state: MathNode
    forward: bool = True       # False = the rule was used right-to-left (an equality)


def shortest_path(source: MathNode, target: MathNode, rules: list[Rule],
                  max_depth: int = 8, *, bidirectional: bool = False) -> list[Step] | None:
    """Breadth-first shortest derivation from ``source`` to ``target``.

    Forward only by default. With ``bidirectional=True`` it may also use the
    reverse direction of a safely-reversible rule (an "uphill" equality move that
    forward search cannot make) — used by the proof-certificate search, whose every
    step is re-validated by ``robust.recheck_proof``. Returns the steps, or
    ``None`` if the goal is not reachable within ``max_depth`` applications.
    """
    if source == target:
        return []
    seen = {source}
    frontier: deque[tuple[MathNode, list[Step]]] = deque([(source, [])])
    while frontier:
        state, trail = frontier.popleft()
        if len(trail) >= max_depth:
            continue
        for app in applications(state, rules, bidirectional=bidirectional):
            if app.result in seen:
                continue
            step = Step(app.rule_id, app.path, app.result, app.forward)
            new_trail = trail + [step]
            if app.result == target:
                return new_trail
            seen.add(app.result)
            frontier.append((app.result, new_trail))
    return None


def all_shortest_paths(source: MathNode, target: MathNode, rules: list[Rule],
                       max_depth: int = 8) -> list[list[Step]]:
    """Every directed derivation of minimal length from ``source`` to ``target``.

    Because the e-graph view knows the goal class, the hinter can enumerate all
    minimal plans and choose a pedagogically natural ordering -- e.g. one that
    clears the ``+0`` before cancelling (Section B.4) -- rather than being forced
    into the single greedy next move.
    """
    first = shortest_path(source, target, rules, max_depth)
    if first is None:
        return []
    depth = len(first)
    found: list[list[Step]] = []
    # BFS keeping ALL trails of length <= depth that reach the target at `depth`.
    frontier: list[tuple[MathNode, list[Step]]] = [(source, [])]
    for _ in range(depth):
        nxt: list[tuple[MathNode, list[Step]]] = []
        for state, trail in frontier:
            for app in applications(state, rules):
                step = Step(app.rule_id, app.path, app.result)
                new_trail = trail + [step]
                if app.result == target:
                    if len(new_trail) == depth:
                        found.append(new_trail)
                else:
                    nxt.append((app.result, new_trail))
        frontier = nxt
    return found
