from __future__ import annotations

from dataclasses import dataclass

from .conditions import SideCondition
from .model import MathNode, from_json, to_json


def wild(name: str) -> MathNode:
    return MathNode("wild", name)


def nonzero(var: str) -> SideCondition:
    return SideCondition("nonzero", var)


@dataclass(frozen=True)
class Rule:
    """One rewrite rule from a BlockDefinition bean."""

    id: str
    owner: str            # the block that owns the rule
    lhs: MathNode         # pattern
    rhs: MathNode         # template
    bidir: bool = False   # B = bidirectional, F = forward-only
    # Guards that must be discharged before the rule may fire.
    conditions: tuple[SideCondition, ...] = ()


# ---------------------------------------------------------------------------
# JSON (de)serialization — so a ruleset can travel in a grading request rather
# than being hardcoded (instructor-authored rules).
# ---------------------------------------------------------------------------
_COND_KINDS = {"nonzero", "positive", "integer", "constant", "notequal"}


def _condition_to_json(c: SideCondition) -> dict:
    d = {"kind": c.kind, "var": c.var}
    if c.arg is not None:
        d["arg"] = c.arg
    return d


def _condition_from_json(d: dict) -> SideCondition:
    kind = d["kind"]
    if kind not in _COND_KINDS:
        raise ValueError(f"unknown side-condition kind {kind!r}")
    return SideCondition(kind, d["var"], d.get("arg"))


def rule_to_json(r: Rule) -> dict:
    return {"id": r.id, "owner": r.owner,
            "lhs": to_json(r.lhs), "rhs": to_json(r.rhs),
            "bidirectional": r.bidir,
            "conditions": [_condition_to_json(c) for c in r.conditions]}


def rule_from_json(d: dict) -> Rule:
    if "id" not in d or "lhs" not in d or "rhs" not in d:
        raise ValueError("rule needs id, lhs, rhs")
    return Rule(str(d["id"]), str(d.get("owner", "")),
                from_json(d["lhs"]), from_json(d["rhs"]),
                bool(d.get("bidirectional", False)),
                tuple(_condition_from_json(c) for c in d.get("conditions", [])))


def ruleset_from_json(items: list[dict]) -> list[Rule]:
    seen: set[str] = set()
    out: list[Rule] = []
    for d in items:
        r = rule_from_json(d)
        if r.id in seen:
            raise ValueError(f"duplicate rule id {r.id!r}")
        seen.add(r.id)
        out.append(r)
    return out
