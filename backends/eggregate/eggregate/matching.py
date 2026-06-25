"""Pattern matching and instantiation over the expression model.

One implementation, shared by every consumer (the hint search, the step
validator, and -- via compilation -- the egglog backend).  Keeping match/
instantiate in a single place is the code-level form of the thesis's "shared
rule source" principle (Section 4.3 / 9): a rule cannot match differently on
the client and the server because there is only one matcher.

Wildcards (block ``wild``, value = name) bind to whole subtrees, with
consistency: the same wildcard name must bind the same subtree everywhere.
There are no binders in the model, so structural equality is the only notion of
sameness (no alpha-equivalence needed; see the thesis scope note).
"""
from __future__ import annotations

from .model import MathNode


def match(pattern: MathNode, node: MathNode,
          env: dict[str, MathNode] | None = None) -> dict[str, MathNode] | None:
    """Match ``pattern`` against ``node``; return wildcard bindings or ``None``."""
    env = {} if env is None else env
    if pattern.op == "wild":
        bound = env.get(pattern.value)
        if bound is None:
            env = dict(env)
            env[pattern.value] = node
            return env
        return env if bound == node else None
    if (pattern.op != node.op or pattern.value != node.value
            or len(pattern.kids) != len(node.kids)):
        return None
    for p, n in zip(pattern.kids, node.kids):
        result = match(p, n, env)
        if result is None:
            return None
        env = result
    return env


def instantiate(template: MathNode, env: dict[str, MathNode]) -> MathNode:
    """Build a concrete tree from ``template`` by substituting bindings."""
    if template.op == "wild":
        return env[template.value]
    if not template.kids:
        return template
    return MathNode(template.op, template.value,
                    tuple(instantiate(k, env) for k in template.kids))
