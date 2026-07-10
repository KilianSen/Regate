"""Sample-solution-guided search (instructor reference derivation).

An instructor authoring an exercise already knows a solution.  Supplying it as a
*reference derivation* -- the sequence of states source = r0, r1, ..., rk = target
-- stabilises everything that is otherwise an unbounded search:

  * **proving** decomposes into k trivial one-hop searches instead of one
    exponential global search (this is the scaling win -- landmarks bound the
    branching factor);
  * **hints** follow the instructor's *intended route* rather than the greedy
    one-ply move the thesis criticises in Section B.4 ("clear the +0 first"
    instead of "cancel because it removes the most structure");
  * **partial credit** measures progress *along the reference* (how far the
    student has travelled toward the goal), not blind distance to the target;
  * the reference itself is **validated** -- each hop must be a real, bounded
    sequence of sound rule applications, so a broken sample solution is caught.

A student who stays on the rail is graded/hinted in O(1) lookups; a student who
diverges is *re-anchored* to the nearest reference waypoint, so search only ever
has to cover the gap back to the rail, never the whole problem.
"""
from __future__ import annotations

from dataclasses import dataclass

from .catalogue import CATALOGUE
from .rule import Rule
from .hints import Step, shortest_path
from .model import MathNode, distance
from .validate import Move, verify_chain


# ---------------------------------------------------------------------------
# The reference derivation.
# ---------------------------------------------------------------------------
@dataclass(frozen=True)
class Reference:
    states: tuple[MathNode, ...]          # r0 = source .. rk = target

    @property
    def source(self) -> MathNode:
        return self.states[0]

    @property
    def target(self) -> MathNode:
        return self.states[-1]

    @property
    def length(self) -> int:
        return len(self.states) - 1


def reference_from_states(states) -> Reference:
    return Reference(tuple(states))


def reference_from_moves(source: MathNode, moves: list[Move]) -> Reference:
    """Build a reference by replaying an instructor's move list."""
    report = verify_chain(source, moves, source)  # goal unused; we only want states
    if not report.valid:
        raise ValueError("instructor moves do not form a valid derivation")
    return Reference(tuple(report.states))


# ---------------------------------------------------------------------------
# Validation: each hop must be a bounded chain of sound rule applications.
# ---------------------------------------------------------------------------
@dataclass
class ReferenceCheck:
    ok: bool
    segments: list[list[Step]]            # recovered fine-grained steps per hop
    bad_hop: int | None = None
    reason: str = ""

    @property
    def fine_steps(self) -> list[Step]:
        return [s for seg in self.segments for s in seg]


def check_reference(ref: Reference, rules: list[Rule] | None = None,
                    max_hop: int = 3) -> ReferenceCheck:
    """Confirm each consecutive pair is connected within ``max_hop`` rule steps.

    Recovers the fine-grained steps (so an instructor may supply only the
    intermediate *states*, even with "macro" hops that skip a few applications).
    """
    rules = CATALOGUE if rules is None else rules
    segments: list[list[Step]] = []
    for i in range(ref.length):
        seg = shortest_path(ref.states[i], ref.states[i + 1], rules, max_depth=max_hop)
        if seg is None:
            return ReferenceCheck(False, segments, bad_hop=i,
                                  reason=f"hop {i}->{i+1} not reachable in {max_hop} steps")
        segments.append(seg)
    return ReferenceCheck(True, segments)


# ---------------------------------------------------------------------------
# Alignment: where on the reference is a (possibly diverged) student state?
# ---------------------------------------------------------------------------
@dataclass
class Alignment:
    index: int          # furthest reference waypoint the state has reached
    kind: str           # 'exact' | 'equivalent' | 'nearest'
    distance: int       # distance to that waypoint (0 if exact)


def align(state: MathNode, ref: Reference) -> Alignment:
    """Locate ``state`` against the reference, preferring the furthest match.

    Alignment is *structural*, not value-based: in an equational derivation every
    state is value-equal to every other, so numeric equivalence cannot measure
    progress -- only closeness of *form* can.
    """
    # exact structural match, furthest first (a student literally on the rail)
    for i in range(ref.length, -1, -1):
        if state == ref.states[i]:
            return Alignment(i, "exact", 0)
    # otherwise the nearest waypoint by tree distance (a diverged student)
    best = min(range(ref.length + 1), key=lambda i: distance(state, ref.states[i]))
    return Alignment(best, "nearest", distance(state, ref.states[best]))


# ---------------------------------------------------------------------------
# Guided proving and hinting.
# ---------------------------------------------------------------------------
def guided_prove(ref: Reference, rules: list[Rule] | None = None,
                 max_hop: int = 3) -> list[Step] | None:
    """A stable, reference-aligned proof source -> target (no global search)."""
    check = check_reference(ref, rules, max_hop)
    return check.fine_steps if check.ok else None


@dataclass
class GuidedHint:
    done: bool
    step: Step | None           # the next concrete move along the reference
    remaining: int              # reference hops left to the goal
    alignment: Alignment


def guided_hint(state: MathNode, ref: Reference, rules: list[Rule] | None = None,
                max_hop: int = 4) -> GuidedHint:
    """The next move from where the student actually is, toward the reference.

    Picks the reference waypoint that minimises *total remaining steps* --
    ``(steps to rejoin the rail at j) + (reference hops from j to the goal)`` --
    and returns the first step of the (bounded) path to it.  A student on the
    rail advances along it; a diverged student is steered back onto it.  Search
    is anchored to nearby waypoints (depth ``max_hop``), never the far target, so
    it stays bounded even when a blind global search would explode.
    """
    rules = CATALOGUE if rules is None else rules
    a = align(state, ref)
    if state == ref.target:
        return GuidedHint(True, None, 0, a)

    k = ref.length
    on_rail = a.index if a.kind == "exact" else None
    lo = (on_rail + 1) if on_rail is not None else 0

    candidates = []
    for j in range(lo, k + 1):
        seg = shortest_path(state, ref.states[j], rules, max_depth=max_hop)
        if not seg:                       # unreachable within max_hop, or already there
            continue
        candidates.append((len(seg) + (k - j), len(seg), seg[0]))
    if not candidates:
        return GuidedHint(False, None, k - a.index, a)   # off the rail, no bounded rejoin
    candidates.sort(key=lambda c: (c[0], c[1]))          # fewest total, then most incremental
    return GuidedHint(False, candidates[0][2], k - a.index, a)


def progress(state: MathNode, ref: Reference) -> float:
    """Fraction of the reference travelled, by alignment (for partial credit)."""
    return align(state, ref).index / ref.length if ref.length else 1.0
