"""The expression model (thesis Section 4.1 / 5.2).

A ``MathNode`` is a typed tree built from a small set of blocks.  Children are
stored in *alphabetical slot order*, which is exactly the path encoding the
thesis uses (Section 5.6): "each integer indexes the flat child list obtained by
visiting slots in alphabetical order".  A fraction therefore exposes
``[denominator, numerator]`` -- index 0 is the denominator, index 1 the
numerator -- so the inner sum ``x + 0`` of ``3*(x+0) / (3*1)`` lives at path
``[1, 1]`` (numerator, then the mul's right child), matching Appendix B.

The same JSON shape (``{"type", "value"?, "slots"?}``) is what ``MathNodeConverter``
persists in Artemis, so these trees round-trip with the real platform data.
"""
from __future__ import annotations

from collections import Counter
from dataclasses import dataclass, field
from typing import Iterator

# Block -> its slot names in ALPHABETICAL order (= the thesis path encoding).
SLOTS: dict[str, tuple[str, ...]] = {
    "number": (),
    "variable": (),
    "add": ("left", "right"),
    "sub": ("left", "right"),
    "mul": ("left", "right"),
    "frac": ("denominator", "numerator"),
    "neg": ("inner",),
    "eq": ("left", "right"),
    # Induction blocks (induction.py): ℕ successor and exponentiation. These are
    # NOT in the shipped catalogue and never reach the egglog oracle / ℚ evaluator;
    # induction is graded by the step-validator only.
    "succ": ("inner",),
    "pow": ("base", "exponent"),
    # 'wild' is a pattern-only block (wildcards a, b, c); see catalogue.py.
    "wild": (),
}

Path = tuple[int, ...]


@dataclass(frozen=True)
class MathNode:
    """An immutable, hashable expression node (whole subtree = its identity)."""

    op: str
    value: str | None = None
    kids: tuple["MathNode", ...] = ()

    # -- slot access by name (independent of storage order) ----------------
    def slot(self, name: str) -> "MathNode":
        return self.kids[SLOTS[self.op].index(name)]

    # -- traversal ---------------------------------------------------------
    def subtrees(self) -> Iterator["MathNode"]:
        """Yield this node and every descendant (each *is* its full subtree)."""
        yield self
        for k in self.kids:
            yield from k.subtrees()

    def at(self, path: Path) -> "MathNode":
        node = self
        for i in path:
            node = node.kids[i]
        return node

    def replace(self, path: Path, new: "MathNode") -> "MathNode":
        if not path:
            return new
        i, rest = path[0], path[1:]
        kids = list(self.kids)
        kids[i] = kids[i].replace(rest, new)
        return MathNode(self.op, self.value, tuple(kids))

    def paths(self, prefix: Path = ()) -> Iterator[Path]:
        yield prefix
        for i, k in enumerate(self.kids):
            yield from k.paths(prefix + (i,))


# ---------------------------------------------------------------------------
# Builders (semantic argument order; storage stays alphabetical).
# ---------------------------------------------------------------------------
def num(v: int | str) -> MathNode:
    return MathNode("number", str(v))


def var(name: str) -> MathNode:
    return MathNode("variable", name)


def add(left: MathNode, right: MathNode) -> MathNode:
    return MathNode("add", kids=(left, right))


def sub(left: MathNode, right: MathNode) -> MathNode:
    return MathNode("sub", kids=(left, right))


def mul(left: MathNode, right: MathNode) -> MathNode:
    return MathNode("mul", kids=(left, right))


def frac(numerator: MathNode, denominator: MathNode) -> MathNode:
    # alphabetical storage: denominator first, numerator second
    return MathNode("frac", kids=(denominator, numerator))


def neg(inner: MathNode) -> MathNode:
    return MathNode("neg", kids=(inner,))


def eq(left: MathNode, right: MathNode) -> MathNode:
    return MathNode("eq", kids=(left, right))


def succ(inner: MathNode) -> MathNode:
    return MathNode("succ", kids=(inner,))


def power(base: MathNode, exponent: MathNode) -> MathNode:
    return MathNode("pow", kids=(base, exponent))


def subst_var(node: "MathNode", name: str, replacement: "MathNode") -> "MathNode":
    """Substitute every ``variable`` named ``name`` with ``replacement`` (used to
    instantiate an induction goal P(var) at 0 and at S(var))."""
    if node.op == "variable" and node.value == name:
        return replacement
    if not node.kids:
        return node
    return MathNode(node.op, node.value, tuple(subst_var(k, name, replacement) for k in node.kids))


# ---------------------------------------------------------------------------
# JSON persistence (the MathNodeConverter shape).
# ---------------------------------------------------------------------------
def to_json(node: MathNode):
    # number/variable carry a value; 'wild' (rule-pattern wildcard) carries its name
    if node.op in ("number", "variable", "wild"):
        return {"type": node.op, "value": node.value}
    slots = {name: [to_json(node.slot(name))] for name in SLOTS[node.op]}
    return {"type": node.op, "slots": slots}


def from_json(obj: dict) -> MathNode:
    t = obj["type"]
    if t in ("number", "variable", "wild"):
        return MathNode(t, str(obj["value"]))
    slots = obj["slots"]
    kids = tuple(from_json(slots[name][0]) for name in SLOTS[t])
    return MathNode(t, None, kids)


# ---------------------------------------------------------------------------
# Pretty printing.
# ---------------------------------------------------------------------------
def _wrap(node: MathNode, heavier_than: set[str]) -> str:
    """Render ``node``, parenthesising it if its operator is in ``heavier_than``."""
    return f"({pretty(node)})" if node.op in heavier_than else pretty(node)


def pretty(node: MathNode) -> str:
    op = node.op
    if op == "number" or op == "variable":
        return node.value or "?"
    if op == "wild":
        return node.value or "?"
    if op == "add":
        return f"{pretty(node.slot('left'))} + {pretty(node.slot('right'))}"
    if op == "sub":
        return f"{pretty(node.slot('left'))} - {pretty(node.slot('right'))}"
    if op == "mul":
        # bind tighter than +,-,= ; also wrap a nested fraction for clarity
        below = {"add", "sub", "eq", "frac"}
        return f"{_wrap(node.slot('left'), below)}·{_wrap(node.slot('right'), below)}"
    if op == "frac":
        # wrap any compound numerator/denominator so the bar's scope is explicit
        below = {"add", "sub", "eq", "mul", "neg"}
        n = _wrap(node.slot("numerator"), below)
        d = _wrap(node.slot("denominator"), below)
        return f"{n}/{d}"
    if op == "neg":
        i = node.slot("inner")
        return f"-({pretty(i)})" if i.kids else f"-{pretty(i)}"
    if op == "eq":
        return f"{pretty(node.slot('left'))} = {pretty(node.slot('right'))}"
    if op == "succ":
        return f"S({pretty(node.slot('inner'))})"
    if op == "pow":
        below = {"add", "sub", "eq", "mul", "frac", "neg"}
        return f"{_wrap(node.slot('base'), below)}^{_wrap(node.slot('exponent'), below)}"
    raise ValueError(f"cannot render {op}")


# ---------------------------------------------------------------------------
# The distance metric (service/MathNodeDistance, Appendix B):
# multiset symmetric difference of all subtrees.
# ---------------------------------------------------------------------------
def distance(a: MathNode, b: MathNode) -> int:
    ca, cb = Counter(a.subtrees()), Counter(b.subtrees())
    diff = ca - cb
    diff.update(cb - ca)
    return sum(diff.values())
