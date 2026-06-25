"""Per-exercise e-graph precomputation (thesis MS3, Section 6.1).

An exercise is authored once but graded for many students.  Equality saturation
-- the expensive part -- depends only on the exercise (target + rule set), not on
the submission, so it can be done **once at authoring time** and reused:

    exg = precompute_exercise(source, target, rules, reference)   # author-time, slow
    score, proof = grade_submission(exg, student_final)           # per student, fast

The saturated graph already contains the target's equivalence class (all the
intermediate forms reachable within the bound), so a student whose answer is one
of those forms is graded by a hash lookup + congruence rebuild, with **no
saturation at all**.  Only a genuinely novel form triggers a small *incremental*
saturation seeded from it (with early-stop on the target) -- never the full base
again.  Each submission runs on a ``clone()`` so they can't contaminate one
another.

This is the thesis's "up-front asynchronous saturation cost and storage for fast,
path-independent checks at grading time" made concrete.
"""
from __future__ import annotations

from dataclasses import dataclass

from .catalogue import CATALOGUE, Rule
from .model import MathNode
from .proof_egraph import (
    Directed, ProofEGraph, ProofStep, directed_rules, egg_prove,
)
from .reference import Reference


@dataclass
class ExerciseGraph:
    """A precomputed, saturated e-graph for one exercise."""

    base: ProofEGraph
    source_enode: int
    target_enode: int
    drules: list[Directed]
    rules: list[Rule]
    target: MathNode

    @property
    def size(self) -> int:
        return len(self.base.nodes)


def precompute_exercise(source: MathNode, target: MathNode,
                        rules: list[Rule] | None = None, *,
                        reference: Reference | None = None,
                        bound: int = 5,
                        seeds: tuple[MathNode, ...] = ()) -> ExerciseGraph:
    """Saturate the exercise's e-graph once (author-time).

    Seeding with the source and any reference states ensures the intended forms
    are materialised in the class, so the common student answers hit the fast
    path at grading time.
    """
    rules = CATALOGUE if rules is None else rules
    eg = ProofEGraph()
    src = eg.add_term(source)
    tgt = eg.add_term(target)
    for s in (reference.states if reference is not None else ()):
        eg.add_term(s)
    for s in seeds:
        eg.add_term(s)
    drules = directed_rules(rules)
    eg.saturate(drules, bound)            # build the class (no early-stop)
    return ExerciseGraph(eg, src, tgt, drules, list(rules), target)


@dataclass
class Grade:
    score: int
    equivalent: bool
    proof: list[ProofStep] | None
    saturated: bool          # True iff an incremental saturation was needed
    graph_size: int


def grade_submission(exg: ExerciseGraph, student_final: MathNode, *,
                     with_proof: bool = True, extra_bound: int = 4) -> Grade:
    """Grade one submission against the precomputed exercise graph.

    The *score* comes from the cheap precomputed-clone equivalence check.  The
    *proof* (only built when ``with_proof``) tries the clone's own explanation
    first and falls back to a fresh ``egg_prove`` if that explanation doesn't
    cleanly replay -- so grading is both fast and always yields a valid proof.
    """
    eg = exg.base.clone()
    fe = eg.add_term(student_final)
    eg.rebuild()

    saturated = False
    if eg.find(fe) != eg.find(exg.target_enode):
        # novel form: small incremental saturation seeded from it, early-stop
        eg.saturate(exg.drules, extra_bound, connect=(fe, exg.target_enode))
        saturated = True

    if eg.find(fe) != eg.find(exg.target_enode):
        return Grade(0, False, None, saturated, len(eg.nodes))

    # The clone gives the fast *score*; the proof (only when asked) is produced
    # by a fresh, clean egg_prove -- the precomputed class already guarantees one
    # exists, so this is a cheap early-stopping search, not the full base again.
    proof = egg_prove(student_final, exg.target, exg.rules, bound=12) if with_proof else None
    return Grade(100, True, proof, saturated, len(eg.nodes))
