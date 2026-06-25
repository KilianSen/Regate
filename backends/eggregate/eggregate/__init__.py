"""Eggregate -- an e-graph reasoning backend (MS3) for the Artemis equational
reasoning exercise type, built on egglog equality saturation.

See the bachelor's thesis "Extending Artemis with proof based mathematical
exercises" (main.pdf), Section 4.5 / 5.7 and Appendix B.
"""
from .model import (
    MathNode, add, distance, eq, frac, from_json, mul, neg, num, pretty, sub,
    to_json, var,
)
from .catalogue import CATALOGUE, Rule, rules
from .conditions import Assumption, SideCondition, discharge
from .matching import instantiate, match
from .backend import EGraphView, equivalent, grade, build_ruleset
from .hints import applications, all_shortest_paths, greedy_hints, shortest_path
from .proof_egraph import ProofEGraph, ProofStep, egg_prove
from .compare import Comparison, compare, print_comparison
from .semantics import evaluate, find_counterexample, free_vars, probably_equal
from .audit import RuleAudit, audit_catalogue, audit_rule
from .robust import (
    Verdict, decide_equivalence, grade_robust, recheck_proof,
    PROVEN_EQUAL, PROVEN_UNEQUAL, EQUAL_NO_CERTIFICATE, UNKNOWN,
)
from .reference import (
    Reference, ReferenceCheck, Alignment, GuidedHint,
    reference_from_states, reference_from_moves, check_reference,
    align, guided_prove, guided_hint, progress,
)
from .precompute import ExerciseGraph, Grade, precompute_exercise, grade_submission
from .validate import (
    Equation, Move, StepResult, apply_equation, apply_rule, verify_chain,
)

__all__ = [
    "MathNode", "add", "sub", "mul", "frac", "neg", "eq", "num", "var",
    "pretty", "distance", "to_json", "from_json",
    "CATALOGUE", "Rule", "rules",
    "Assumption", "SideCondition", "discharge", "match", "instantiate",
    "EGraphView", "equivalent", "grade", "build_ruleset",
    "applications", "greedy_hints", "shortest_path", "all_shortest_paths",
    "ProofEGraph", "ProofStep", "egg_prove",
    "Comparison", "compare", "print_comparison",
    "evaluate", "find_counterexample", "free_vars", "probably_equal",
    "RuleAudit", "audit_catalogue", "audit_rule",
    "Verdict", "decide_equivalence", "grade_robust", "recheck_proof",
    "PROVEN_EQUAL", "PROVEN_UNEQUAL", "EQUAL_NO_CERTIFICATE", "UNKNOWN",
    "Reference", "ReferenceCheck", "Alignment", "GuidedHint",
    "reference_from_states", "reference_from_moves", "check_reference",
    "align", "guided_prove", "guided_hint", "progress",
    "ExerciseGraph", "Grade", "precompute_exercise", "grade_submission",
    "Equation", "Move", "StepResult", "apply_rule", "apply_equation", "verify_chain",
]
