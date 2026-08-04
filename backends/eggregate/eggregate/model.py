"""The expression model.

A ``MathNode`` is a typed tree built from a small set of blocks.  Children are
stored in *alphabetical slot order*, which is exactly the path encoding used:
"each integer indexes the flat child list obtained by
visiting slots in alphabetical order".  A fraction therefore exposes
``[denominator, numerator]`` -- index 0 is the denominator, index 1 the
numerator -- so the inner sum ``x + 0`` of ``3*(x+0) / (3*1)`` lives at path
``[1, 1]`` (numerator, then the mul's right child).

The JSON shape (``{"type", "value"?, "slots"?}``) is a plain typed-tree any host
can produce; it is deliberately compatible with the format the reference adopter
(Artemis, via its ``MathNodeConverter``) persists, so these trees round-trip with
real platform data without binding the backend to any one platform.
"""
from __future__ import annotations

from collections import Counter
from dataclasses import dataclass, field
from typing import Iterator

# Block -> its slot names in ALPHABETICAL order (= the path encoding).
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
    # n-ary NAMED function application (protocol 1.1). Its single slot 'args' holds
    # an ORDERED LIST of arbitrary length rather than one child, and `value` carries
    # the function name -- see VARIADIC below. The path encoding is unchanged: the
    # flat child list of an `apply` is exactly its args, in order.
    "apply": ("args",),
}

# Blocks whose (single) slot holds a list of children instead of exactly one.
# Everything downstream of `kids` is already n-ary (MathNode.kids is a tuple, and
# matching/instantiation/replace/paths compare arities), so this set is only
# consulted by the JSON (de)serializer and the slot-name accessor.
VARIADIC: frozenset[str] = frozenset({"apply"})

Path = tuple[int, ...]


@dataclass(frozen=True)
class MathNode:
    """An immutable, hashable expression node (whole subtree = its identity)."""

    op: str
    value: str | None = None
    kids: tuple["MathNode", ...] = ()

    # -- slot access by name (independent of storage order) ----------------
    def slot(self, name: str) -> "MathNode":
        if self.op in VARIADIC:
            # A variadic slot is a list, not a child: refuse rather than silently
            # hand back kids[0] and let a caller mistake it for "the" argument.
            raise ValueError(f"{self.op!r} has a variadic slot; use .kids")
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


def apply(name: str, *args: MathNode) -> MathNode:
    """A named n-ary function application, ``name(args...)`` (protocol 1.1).

    The function carries no built-in meaning: it is defined by the request's
    recursive ``definitions`` (rules whose LHS is this ``apply`` shape)."""
    return MathNode("apply", name, tuple(args))


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
    if node.op in VARIADIC:
        # `apply`: one slot holding the ordered argument list; `value` is the
        # function name.
        (slot_name,) = SLOTS[node.op]
        return {"type": node.op, "value": node.value,
                "slots": {slot_name: [to_json(k) for k in node.kids]}}
    slots = {name: [to_json(node.slot(name))] for name in SLOTS[node.op]}
    return {"type": node.op, "slots": slots}


def from_json(obj: dict) -> MathNode:
    t = obj["type"]
    if t not in SLOTS:
        raise ValueError(f"unknown node type {t!r}")
    if t in ("number", "variable", "wild"):
        return MathNode(t, str(obj["value"]))
    slots = obj["slots"]
    if t in VARIADIC:
        (slot_name,) = SLOTS[t]
        name = obj.get("value")
        if not isinstance(name, str) or not name:
            raise ValueError(f"{t!r} requires a non-empty string 'value' "
                             f"(the function name), got {name!r}")
        args = slots[slot_name]
        if not isinstance(args, (list, tuple)):
            raise ValueError(f"{t!r} slot {slot_name!r} must be a list of arguments")
        return MathNode(t, name, tuple(from_json(a) for a in args))
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
    if op == "apply":
        return f"{node.value or '?'}({', '.join(pretty(k) for k in node.kids)})"
    raise ValueError(f"cannot render {op}")


# ---------------------------------------------------------------------------
# AC normalisation (mirrors the frontend's expr.normalizeAC): flatten + sort the
# commutative/associative chains of `+` and `·` into one canonical tree, so two
# expressions equal up to associativity/commutativity normalise identically.
# Used only when an exercise sets `options.ac_normalization` -- it never affects
# step validation, only "is this the target form / are these equal up to AC".
# ---------------------------------------------------------------------------
def _struct_key(node: "MathNode") -> str:
    return f"{node.op}|{node.value or ''}(" + ",".join(_struct_key(k) for k in node.kids) + ")"


def ac_normalize(node: "MathNode") -> "MathNode":
    kids = tuple(ac_normalize(k) for k in node.kids)
    node = MathNode(node.op, node.value, kids)
    if node.op in ("add", "mul"):
        parts: list[MathNode] = []

        def collect(n: MathNode) -> None:
            if n.op == node.op:
                for k in n.kids:
                    collect(k)
            else:
                parts.append(n)

        collect(node)
        parts.sort(key=_struct_key)
        acc = parts[0]
        for p in parts[1:]:                       # rebuild as a left-nested chain
            acc = MathNode(node.op, None, (acc, p))
        return acc
    return node


# ---------------------------------------------------------------------------
# The distance metric (service/MathNodeDistance):
# multiset symmetric difference of all subtrees.
# ---------------------------------------------------------------------------
def distance(a: MathNode, b: MathNode) -> int:
    ca, cb = Counter(a.subtrees()), Counter(b.subtrees())
    diff = ca - cb
    diff.update(cb - ca)
    return sum(diff.values())
