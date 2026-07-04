"""The e-graph reasoning backend (thesis Section 4.5 / 5.7, milestone MS3).

This is the "second engine" of Section 4.3.  It compiles the shared rule
catalogue (``catalogue.py``) into an egglog ruleset, runs *bounded* equality
saturation (Section 6.3: saturation needs termination/resource bounds), and
answers two questions:

  * ``equivalent(s, t)`` / ``grade(...)`` -- are two expressions in the same
    e-class?  This is equivalence-based grading: it accepts *any* valid
    derivation, not just a replay of one stored chain (Section 4.4 / B.3).

  * ``EGraphView`` -- the saturated e-graph itself, so a hint can rank a whole
    path to the goal rather than a single next move (Section B.4), and so the
    e-class can be dumped (the illustrative figure the B.4 TODO asks for).

The compilation is what makes "single shared rule source, two engines" literal:
forward (F) rules become a one-directional ``rewrite``; bidirectional (B) rules
become a ``birewrite``; a ``NotEqualToConstant`` constraint binds the wildcard to
an ``i64`` literal guarded by ``ne(.., 0)``.
"""
from __future__ import annotations

from egglog import (
    EGraph,
    Expr,
    birewrite,
    eq,
    i64,
    i64Like,
    ne,
    rewrite,
    ruleset,
    var,
)
from egglog import StringLike

from .catalogue import CATALOGUE
from .rule import Rule
from .model import MathNode


# --- the egglog datatype mirroring the expression model --------------------
class Math(Expr):
    def __init__(self, value: i64Like) -> None: ...          # Number
    @classmethod
    def named(cls, name: StringLike) -> "Math": ...          # Variable
    def __add__(self, other: "Math") -> "Math": ...          # Add
    def __sub__(self, other: "Math") -> "Math": ...          # Sub
    def __mul__(self, other: "Math") -> "Math": ...          # Mul
    def __truediv__(self, other: "Math") -> "Math": ...      # Fraction
    def __neg__(self) -> "Math": ...                         # Negation
    def equals(self, other: "Math") -> "Math": ...           # Equality block


def _to_egglog(node: MathNode, env: dict):
    """Translate a model node (possibly with wildcards) into an egglog term."""
    op = node.op
    if op == "wild":
        return env[node.value]
    if op == "number":
        return Math(int(node.value))
    if op == "variable":
        return Math.named(node.value)
    k = [_to_egglog(c, env) for c in node.kids]
    if op == "add":
        return k[0] + k[1]
    if op == "sub":
        return k[0] - k[1]
    if op == "mul":
        return k[0] * k[1]
    if op == "frac":
        # storage order is (denominator, numerator); term is numerator/denominator
        return k[1] / k[0]
    if op == "neg":
        return -k[0]
    if op == "eq":
        return k[0].equals(k[1])
    raise ValueError(f"cannot translate {op}")


def to_math(node: MathNode):
    """Translate a concrete (wildcard-free) expression."""
    return _to_egglog(node, {})


def _wild_names(node: MathNode, acc: set[str]) -> set[str]:
    if node.op == "wild":
        acc.add(node.value)
    for k in node.kids:
        _wild_names(k, acc)
    return acc


def _compile(rule: Rule):
    """Compile one catalogue rule into an egglog rewrite/birewrite.

    The equivalence oracle stays *sound*: a guard is only enforceable here when
    it is literal-decidable (a ``nonzero``/``notequal`` on a number, compiled to
    egglog's ``ne``).  Such a wildcard is therefore bound to an ``i64`` literal,
    so the rule fires only on concrete numbers.  Guards that need symbolic
    reasoning (nonzero of a variable, positivity, ...) are NOT compiled into the
    theory -- the e-graph must not bless e.g. ``x/x = 1`` for unknown ``x``.
    Those guards are discharged instead by the step validator against the
    student's declared assumptions (see validate.py).
    """
    numeric_guard = {
        c.var: c for c in rule.conditions if c.kind in ("nonzero", "notequal")
    }
    names = _wild_names(rule.lhs, set()) | _wild_names(rule.rhs, set())
    env: dict = {}
    conds = []
    for name in sorted(names):
        if name in numeric_guard:
            g = numeric_guard[name]
            cv = var(f"{rule.id}__{name}", i64)
            env[name] = Math(cv)
            conds.append(ne(cv).to(i64(g.arg or 0)))
        else:
            env[name] = var(f"{rule.id}__{name}", Math)
    # A rule whose guard cannot be compiled (e.g. symbolic nonzero) is kept out
    # of the sound oracle entirely.
    if any(c.kind not in ("nonzero", "notequal") for c in rule.conditions):
        return None
    lhs = _to_egglog(rule.lhs, env)
    rhs = _to_egglog(rule.rhs, env)
    # egglog forbids rewriting *from* a lone variable (it is ungrounded and
    # non-terminating).  A rule like neg_neg (-(-a) <-> a) therefore cannot be a
    # birewrite; compile it as a forward rewrite from the structured side.  The
    # union it creates is symmetric in the e-graph, so equivalence is preserved.
    lhs_lone = rule.lhs.op == "wild"
    rhs_lone = rule.rhs.op == "wild"
    if rule.bidir and not conds and not lhs_lone and not rhs_lone:
        return birewrite(lhs).to(rhs)
    if lhs_lone and not rhs_lone:
        lhs, rhs = rhs, lhs  # rewrite from the structured side
    return rewrite(lhs).to(rhs, *conds)


def build_ruleset(rules: list[Rule] | None = None):
    """Compile the (shared) catalogue into an egglog ruleset.

    Rules whose guards are not soundly compilable are dropped (``_compile``
    returns ``None``); they live only in the step validator.
    """
    rules = CATALOGUE if rules is None else rules
    compiled = [c for c in (_compile(r) for r in rules) if c is not None]
    return ruleset(*compiled)


# The full theory, compiled once.
THEORY = build_ruleset()

# Bounded saturation: bidirectional assoc/comm/distrib have no finite fixpoint
# and the e-graph grows combinatorially, so we run a fixed number of iterations
# instead of saturate().  This is the "termination/resource bound" MS3 requires
# (Section 6.3).  Empirically the worked example's equivalence is found by
# iteration 3; beyond ~5 the distributivity/AC blow-up dominates with no benefit,
# so 5 is a safe default for small classroom expressions.  Raise it per call only
# when an exercise genuinely needs deeper rewriting, and expect cost to climb.
DEFAULT_BOUND = 5


class EGraphView:
    """A saturated e-graph over one or more seed expressions."""

    def __init__(self, *seeds: MathNode, rules: list[Rule] | None = None,
                 bound: int = DEFAULT_BOUND):
        self.egraph = EGraph()
        self._terms = {}
        rs = THEORY if rules is None else build_ruleset(rules)
        for i, s in enumerate(seeds):
            t = to_math(s)
            self.egraph.let(f"seed{i}", t)
            self._terms[s] = t
        self.egraph.run(rs * bound)

    def _term(self, node: MathNode):
        t = self._terms.get(node)
        if t is None:
            t = to_math(node)
            self.egraph.let(f"q{len(self._terms)}", t)
            self._terms[node] = t
        return t

    def same_class(self, x: MathNode, y: MathNode) -> bool:
        try:
            self.egraph.check(eq(self._term(x)).to(self._term(y)))
            return True
        except Exception:
            return False


def equivalent(x: MathNode, y: MathNode, rules: list[Rule] | None = None,
               bound: int = DEFAULT_BOUND) -> bool:
    """Are ``x`` and ``y`` provably equal under the (bounded) rule theory?"""
    view = EGraphView(x, y, rules=rules, bound=bound)
    return view.same_class(x, y)


def grade(student_final: MathNode, target: MathNode,
          rules: list[Rule] | None = None, bound: int = DEFAULT_BOUND) -> int:
    """Equivalence-based grade: 100 iff the final state reaches the goal class.

    Path-independent -- unlike RewriteChainGrader it does not replay or even look
    at the intermediate steps; it asks only whether the endpoints coincide in the
    saturated e-graph (thesis Section 4.4, the second grader bean).
    """
    return 100 if equivalent(student_final, target, rules=rules, bound=bound) else 0
