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

    # --- `apply`: n-ary NAMED function application (protocol 1.1) -----------
    # egglog functions are fixed-arity, so the n-ary `apply` node is encoded as
    # one egglog constructor per arity, with the function name carried as a
    # String argument. That keeps the encoding *data-driven*: a host adds a new
    # binary operator by sending an `apply` node plus its `definitions`, and no
    # egglog declaration changes. Congruence is exactly right -- `call2("f",x,y)`
    # and `call2("f",x',y')` are merged iff the name matches and the arguments
    # are in the same e-classes -- and two different names can never be confused,
    # because the String literal is part of the term.
    @classmethod
    def call0(cls, fn: StringLike) -> "Math": ...
    @classmethod
    def call1(cls, fn: StringLike, a0: "Math") -> "Math": ...
    @classmethod
    def call2(cls, fn: StringLike, a0: "Math", a1: "Math") -> "Math": ...
    @classmethod
    def call3(cls, fn: StringLike, a0: "Math", a1: "Math", a2: "Math") -> "Math": ...
    @classmethod
    def call4(cls, fn: StringLike, a0: "Math", a1: "Math", a2: "Math",
              a3: "Math") -> "Math": ...


# Arities of `apply` the theory can hold. An application wider than this is not
# translatable, so the oracle simply declines (ValueError -> `equivalent` returns
# False -> UNKNOWN); it is never graded wrong.
_CALL = (Math.call0, Math.call1, Math.call2, Math.call3, Math.call4)
MAX_APPLY_ARITY = len(_CALL) - 1


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
    if op == "apply":
        if len(k) > MAX_APPLY_ARITY:
            raise ValueError(f"apply arity {len(k)} exceeds {MAX_APPLY_ARITY}")
        if not node.value:
            raise ValueError("apply without a function name")
        return _CALL[len(k)](node.value, *k)
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
    returns ``None``); they live only in the step validator. Rules the egglog
    signature cannot express at all are dropped too, per-rule rather than
    failing the whole theory.
    """
    rules = CATALOGUE if rules is None else rules
    compiled = []
    for r in rules:
        try:
            c = _compile(r)
        except ValueError:
            # Outside the egglog signature (e.g. an `apply` wider than
            # MAX_APPLY_ARITY, or a `succ`/`pow` induction op). Dropping the rule
            # only ever weakens the oracle, which reads a miss as "not proven".
            continue
        if c is not None:
            compiled.append(c)
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
    """Are ``x`` and ``y`` provably equal under the (bounded) rule theory?

    A term outside the egglog signature (``pow``, ``succ`` — the induction ops the
    theory does not model) simply yields no oracle evidence. Returning ``False``
    is the sound direction: the oracle can only ever *fail* to see an equality,
    and ``decide_equivalence`` reads that as UNKNOWN, never as "unequal".
    """
    try:
        view = EGraphView(x, y, rules=rules, bound=bound)
        return view.same_class(x, y)
    except ValueError:                  # cannot translate an op into the theory
        return False


def grade(student_final: MathNode, target: MathNode,
          rules: list[Rule] | None = None, bound: int = DEFAULT_BOUND) -> int:
    """Equivalence-based grade: 100 iff the final state reaches the goal class.

    Path-independent -- unlike RewriteChainGrader it does not replay or even look
    at the intermediate steps; it asks only whether the endpoints coincide in the
    saturated e-graph (thesis Section 4.4, the second grader bean).
    """
    return 100 if equivalent(student_final, target, rules=rules, bound=bound) else 0
