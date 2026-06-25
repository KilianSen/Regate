"""Run both proving backends on the same goal and compare them.

Two execution modes for the same question ("is source == target, and why?"):

  * ``bfs``  -- ``hints.shortest_path``: searches forward rule applications,
    returns a **minimal** chain, but only over the forward-directed fragment it
    explores (no symmetric/uphill moves).
  * ``egg``  -- ``proof_egraph.egg_prove``: saturates an e-graph and reads a
    proof off the provenance structure; handles symmetric and congruence-driven
    equalities, but the proof is **not guaranteed minimal**.

``compare`` runs both, times them, and reports where they agree and differ --
making concrete the trade-off discussed in the design notes (minimal-but-narrow
search vs. complete-but-non-minimal saturation).
"""
from __future__ import annotations

from dataclasses import dataclass
from time import perf_counter

from .catalogue import Rule
from .hints import shortest_path
from .model import MathNode, Path, pretty
from .proof_egraph import egg_prove


@dataclass(frozen=True)
class NormStep:
    rule_id: str
    path: Path
    state: MathNode


@dataclass
class BackendResult:
    name: str
    found: bool
    seconds: float
    steps: list[NormStep] | None

    @property
    def n_steps(self) -> int | None:
        return None if self.steps is None else len(self.steps)


@dataclass
class Comparison:
    source: MathNode
    target: MathNode
    bfs: BackendResult
    egg: BackendResult

    @property
    def agree(self) -> bool:
        return self.bfs.found == self.egg.found

    @property
    def same_length(self) -> bool:
        return (self.bfs.found and self.egg.found
                and self.bfs.n_steps == self.egg.n_steps)


def _run_bfs(source, target, rules, max_depth) -> BackendResult:
    t0 = perf_counter()
    path = shortest_path(source, target, rules, max_depth=max_depth)
    dt = perf_counter() - t0
    if path is None:
        return BackendResult("bfs", False, dt, None)
    steps = [NormStep(s.rule_id, s.path, s.state) for s in path]
    return BackendResult("bfs", True, dt, steps)


def _run_egg(source, target, rules, bound) -> BackendResult:
    t0 = perf_counter()
    proof = egg_prove(source, target, rules, bound=bound)
    dt = perf_counter() - t0
    if proof is None:
        return BackendResult("egg", False, dt, None)
    steps = [NormStep(s.rule_id, s.path, s.state) for s in proof]
    return BackendResult("egg", True, dt, steps)


def compare(source: MathNode, target: MathNode, rules: list[Rule], *,
            max_depth: int = 8, bound: int = 12) -> Comparison:
    return Comparison(
        source, target,
        _run_bfs(source, target, rules, max_depth),
        _run_egg(source, target, rules, bound),
    )


def _fmt(r: BackendResult) -> str:
    if not r.found:
        return f"no proof within budget   ({r.seconds * 1e3:.1f} ms)"
    return f"{r.n_steps} steps   ({r.seconds * 1e3:.1f} ms)"


def print_comparison(c: Comparison) -> None:
    print(f"  {pretty(c.source)}  ==  {pretty(c.target)} ?")
    print(f"    bfs (minimal search) : {_fmt(c.bfs)}")
    print(f"    egg (saturate+prove) : {_fmt(c.egg)}")
    if not c.agree:
        winner = "egg" if c.egg.found else "bfs"
        print(f"    -> DISAGREE on existence: only {winner} found a proof")
    elif c.bfs.found:
        if c.same_length:
            print("    -> agree; same length")
        else:
            print(f"    -> agree; egg proof is {c.egg.n_steps - c.bfs.n_steps} "
                  f"step(s) longer (egg proofs are not minimal)")
    else:
        print("    -> agree; neither finds a proof")
    for r in (c.bfs, c.egg):
        if r.found:
            chain = " -> ".join(pretty(s.state) for s in r.steps)
            print(f"      {r.name}: {pretty(c.source)} -> {chain}")
