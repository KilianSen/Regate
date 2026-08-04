"""A proof-producing e-graph (egg-style ``explain_equivalence``, in Python).

This is the second proving backend.  Where ``hints.shortest_path`` *searches*
the rewrite space and returns a minimal chain, this backend *saturates* an
e-graph and then reads a proof off a provenance structure -- the way egg does it
(Flatt et al., "Small Proofs from Congruence Closure", FMCAD 2022):

  1. a union-find over e-nodes with congruence closure (``rebuild``);
  2. rules applied by e-matching, each union justified by the rule that caused
     it (or by *congruence* when two ``f(...)`` nodes merge because their
     children merged);
  3. ``explain`` walks the provenance graph between the two terms and turns it
     into a flat sequence of rewrites -- congruence edges recurse into the child
     position that changed, which is exactly what yields the rewrite *path*.

Every e-node remembers the concrete term it was built from (``term_of``), so the
proof is reconstructed from real terms (no lossy extraction), and the result is
replayed to assert it actually transforms source into target.

Unlike BFS the proof is **not guaranteed minimal** (egg's isn't either); the
comparison harness in ``compare.py`` makes that visible.
"""
from __future__ import annotations

from collections import defaultdict, deque
from dataclasses import dataclass, field

from .rule import Rule
from .conditions import DISCHARGED, discharge
from .matching import instantiate, match
from .model import MathNode, Path


# ---------------------------------------------------------------------------
# Directed rules (mirrors backend._compile: forward always; backward only for a
# safe bidirectional rule -- no guard, neither side a lone wildcard).
# ---------------------------------------------------------------------------
@dataclass(frozen=True)
class Directed:
    rule_id: str
    pattern: MathNode
    template: MathNode
    forward: bool
    conditions: tuple = ()


def _guards_ok(dr: Directed, subst: dict, term_of, assumptions: frozenset) -> bool:
    """Every guard of ``dr`` discharged under ``subst`` -- from the literal bound
    to it, or from a declared assumption. A guard on a wildcard this direction's
    pattern does not bind is undecidable, so the rule cannot fire."""
    for c in dr.conditions:
        cls = subst.get(c.var)
        if cls is None or discharge(c, term_of[cls], assumptions) != DISCHARGED:
            return False
    return True


def directed_rules(rules: list[Rule]) -> list[Directed]:
    out: list[Directed] = []
    for r in rules:
        out.append(Directed(r.id, r.lhs, r.rhs, True, r.conditions))
        if (r.bidir and not r.conditions
                and r.lhs.op != "wild" and r.rhs.op != "wild"):
            out.append(Directed(r.id, r.rhs, r.lhs, False, ()))
    return out


# ---------------------------------------------------------------------------
# Provenance justifications.
# ---------------------------------------------------------------------------
@dataclass(frozen=True)
class RuleJust:
    rule_id: str
    lhs_side: int     # the e-node on the rule's LHS side (for direction display)
    forward: bool     # whether the stored application was the rule's forward dir


@dataclass(frozen=True)
class CongJust:
    pass


CONG = CongJust()


@dataclass(frozen=True)
class ENode:
    op: str
    value: str | None
    children: tuple[int, ...]


class ProofEGraph:
    def __init__(self) -> None:
        self.parent: list[int] = []
        self.nodes: list[ENode] = []
        self.term_of: list[MathNode] = []
        self.hashcons: dict[tuple, int] = {}
        self.adj: dict[int, list[tuple[int, object]]] = defaultdict(list)

    # -- union-find -------------------------------------------------------
    def find(self, i: int) -> int:
        while self.parent[i] != i:
            self.parent[i] = self.parent[self.parent[i]]
            i = self.parent[i]
        return i

    def _key(self, op, value, children) -> tuple:
        return (op, value, tuple(self.find(c) for c in children))

    def _canon(self, i: int) -> tuple:
        n = self.nodes[i]
        return (n.op, n.value, tuple(self.find(c) for c in n.children))

    # -- construction -----------------------------------------------------
    def add_node(self, op, value, children, term: MathNode) -> int:
        key = self._key(op, value, children)
        hit = self.hashcons.get(key)
        if hit is not None:
            return self.find(hit)
        i = len(self.nodes)
        self.nodes.append(ENode(op, value, tuple(children)))
        self.term_of.append(term)
        self.parent.append(i)
        self.hashcons[key] = i
        return i

    def add_term(self, node: MathNode) -> int:
        children = tuple(self.add_term(k) for k in node.kids)
        return self.add_node(node.op, node.value, children, node)

    # -- equality with provenance ----------------------------------------
    def union(self, a: int, b: int, just: object) -> bool:
        ra, rb = self.find(a), self.find(b)
        if ra == rb:
            return False
        # record the provenance edge between the *specific* e-nodes a, b
        self.adj[a].append((b, just))
        self.adj[b].append((a, just))
        self.parent[rb] = ra
        return True

    def clone(self) -> "ProofEGraph":
        """A cheap structural copy (ENodes/terms are immutable and shared).

        Used to precompute a base e-graph once and grade each submission on a
        throw-away copy, so submissions never contaminate one another."""
        e = ProofEGraph()
        e.parent = list(self.parent)
        e.nodes = list(self.nodes)        # ENode is frozen -> shareable
        e.term_of = list(self.term_of)    # MathNode is frozen -> shareable
        e.hashcons = dict(self.hashcons)
        e.adj = defaultdict(list, {k: list(v) for k, v in self.adj.items()})
        return e

    def rebuild(self) -> None:
        """Congruence closure: merge e-nodes that became equal by their children."""
        changed = True
        while changed:
            changed = False
            seen: dict[tuple, int] = {}
            for i in range(len(self.nodes)):
                key = self._canon(i)
                j = seen.get(key)
                if j is None:
                    seen[key] = i
                elif self.find(i) != self.find(j):
                    self.union(i, j, CONG)
                    changed = True
        self.hashcons = {self._canon(i): self.find(i) for i in range(len(self.nodes))}

    def members(self) -> dict[int, list[int]]:
        m: dict[int, list[int]] = defaultdict(list)
        for i in range(len(self.nodes)):
            m[self.find(i)].append(i)
        return m

    # -- e-matching -------------------------------------------------------
    def _match_node(self, pat: MathNode, i: int, subst: dict, members):
        if pat.op == "wild":
            cls = self.find(i)
            if pat.value in subst:
                return [subst] if self.find(subst[pat.value]) == cls else []
            s = dict(subst)
            s[pat.value] = i
            return [s]
        n = self.nodes[i]
        if n.op != pat.op or n.value != pat.value or len(n.children) != len(pat.kids):
            return []
        substs = [subst]
        for pk, child in zip(pat.kids, n.children):
            nxt = []
            for s in substs:
                nxt.extend(self._match_class(pk, child, s, members))
            substs = nxt
        return substs

    def _match_class(self, pat: MathNode, cls_member: int, subst: dict, members):
        if pat.op == "wild":
            cls = self.find(cls_member)
            if pat.value in subst:
                return [subst] if self.find(subst[pat.value]) == cls else []
            s = dict(subst)
            s[pat.value] = cls_member
            return [s]
        out = []
        for j in members[self.find(cls_member)]:
            out.extend(self._match_node(pat, j, subst, members))
        return out

    # -- saturation -------------------------------------------------------
    def saturate(self, drules: list[Directed], bound: int,
                 connect: tuple[int, int] | None = None,
                 max_nodes: int = 60_000,
                 assumptions: frozenset = frozenset()) -> dict:
        """Run bounded equality saturation.

        If ``connect=(a, b)`` is given, stop as soon as the two are in the same
        class -- proving needs only enough saturation to *link* the endpoints,
        not a full fixpoint, which keeps the AC/distributivity blow-up at bay.
        ``max_nodes`` is a hard resource bound (the thesis's Section 6.3 concern).
        ``assumptions`` are the exercise's declared facts, which is what lets a
        guarded rule fire on a symbolic binding (``x/x -> 1`` under ``x != 0``).

        Returns a record of WHY the run ended, because "the e-node count stopped
        growing" is not by itself evidence of convergence:

        ``stop``       ``connected`` | ``fixpoint`` | ``starved`` | ``node_cap`` | ``bound``
        ``rounds``     iterations actually run
        ``truncated``  some round's match collection hit the budget below

        ``fixpoint`` means no rewrite fired from a COMPLETE match set. When the
        match list was truncated, a round in which nothing fired only says the
        collected prefix was redundant, so that case reports ``starved`` instead --
        measured: at m=4 the truncated run saw 60_000 of 867_767 matches and looked
        converged at round 7, while the untruncated round 6 grew 23_604 -> 60_001
        e-nodes. Callers reporting iterations-to-fixpoint must reject ``starved``.
        """
        self.rebuild()
        if connect and self.find(connect[0]) == self.find(connect[1]):
            return {"stop": "connected", "rounds": 0, "truncated": False,
                    "nodes": len(self.nodes)}
        truncated = False
        stop = "bound"
        rounds = 0
        for _ in range(bound):
            rounds += 1
            members = self.members()
            # The match list is bounded too. Collecting every match before applying any of them
            # is its own memory sink, independent of graph growth: matches scale as
            # nodes x rules x substitutions, so at 60k nodes this list alone reached multiple GB
            # (capping only `add_term` below cut fixture 31 from ~20 GB to ~5 GB and still climbing).
            # `max_nodes` rewrites per iteration is already far more than a bounded run can use.
            app_budget = max_nodes
            applications = []
            for dr in drules:
                if len(applications) >= app_budget:
                    truncated = True
                    break
                for i in range(len(self.nodes)):
                    if len(applications) >= app_budget:
                        truncated = True
                        break
                    for subst in self._match_node(dr.pattern, i, {}, members):
                        if dr.conditions and not _guards_ok(dr, subst, self.term_of,
                                                            assumptions):
                            continue
                        applications.append((dr, i, subst))
                        if len(applications) >= app_budget:
                            truncated = True
                            break
            did = False
            for dr, i, subst in applications:
                # Enforce the cap HERE, not only after the iteration. Every `add_term` below
                # grows the graph, and one iteration can apply tens of thousands of rewrites, so
                # checking only between iterations lets a single pass blow straight past the
                # bound: measured 23_604 -> 305_180 e-nodes in one step (5x over the cap), and
                # ~20 GB resident on conformance fixture 31 before the OS intervened. Since
                # AC/distributivity have no finite fixpoint, this cap is the ONLY thing bounding
                # memory, so it has to hold inside the loop. Stopping early is sound: bounded
                # saturation already means "not proven within the bound", never "unequal".
                if len(self.nodes) > max_nodes:
                    break
                term_subst = {k: self.term_of[v] for k, v in subst.items()}
                rhs_term = instantiate(dr.template, term_subst)
                rhs = self.add_term(rhs_term)
                if self.union(i, rhs, RuleJust(dr.rule_id, i, dr.forward)):
                    did = True
            self.rebuild()
            if connect and self.find(connect[0]) == self.find(connect[1]):
                stop = "connected"
                break
            # Order matters: the node cap is the stronger claim, so it is checked first. A round
            # that fired nothing off a truncated match list is `starved`, never `fixpoint`.
            if len(self.nodes) > max_nodes:
                stop = "node_cap"
                break
            if not did:
                stop = "starved" if truncated else "fixpoint"
                break
        return {"stop": stop, "rounds": rounds, "truncated": truncated,
                "nodes": len(self.nodes)}

    # -- provenance path --------------------------------------------------
    def _path(self, a: int, b: int):
        """Shortest provenance path a..b as a list of (u, v, just)."""
        if a == b:
            return []
        prev: dict[int, tuple[int, object]] = {a: (a, None)}
        q = deque([a])
        while q:
            u = q.popleft()
            if u == b:
                break
            for v, just in self.adj[u]:
                if v not in prev:
                    prev[v] = (u, just)
                    q.append(v)
        if b not in prev:
            return None
        edges = []
        cur = b
        while cur != a:
            p, just = prev[cur]
            edges.append((p, cur, just))
            cur = p
        edges.reverse()
        return edges

    # -- explanation (flat rewrite instructions) --------------------------
    def explain(self, ea: int, eb: int):
        edges = self._path(ea, eb)
        if edges is None:
            return None
        instrs: list[tuple[str, bool, Path, int]] = []
        for u, v, just in edges:
            self._expand(u, v, just, (), instrs)
        return instrs

    def _expand(self, u, v, just, prefix, out):
        if isinstance(just, RuleJust):
            eff_forward = just.forward if u == just.lhs_side else not just.forward
            out.append((just.rule_id, eff_forward, prefix, v))
            return
        # congruence: recurse into the child positions that differ
        nu, nv = self.nodes[u], self.nodes[v]
        for i, (cu, cv) in enumerate(zip(nu.children, nv.children)):
            if cu == cv or self.find(cu) != self.find(cv):
                continue
            sub = self._path(cu, cv)
            if not sub:
                continue
            for su, sv, sj in sub:
                self._expand(su, sv, sj, prefix + (i,), out)


# ---------------------------------------------------------------------------
# High-level proving backend.
# ---------------------------------------------------------------------------
@dataclass(frozen=True)
class ProofStep:
    rule_id: str
    forward: bool        # direction the rule was used (an equality, not a legal-move claim)
    path: Path
    state: MathNode      # the line after this step


def egg_prove(source: MathNode, target: MathNode, rules: list[Rule],
              bound: int = 30,
              assumptions: frozenset = frozenset()) -> list[ProofStep] | None:
    """Prove source == target by saturation + provenance explanation.

    Returns the rewrite chain (concrete states), or ``None`` if the two are not
    equal within the saturation bound.  The chain is replayed from ``source`` via
    the provenance instructions and asserted to reach ``target``.
    """
    eg = ProofEGraph()
    ea = eg.add_term(source)
    eb = eg.add_term(target)
    eg.saturate(directed_rules(rules), bound, connect=(ea, eb), assumptions=assumptions)
    if eg.find(ea) != eg.find(eb):
        return None
    steps = replay_explanation(eg, source, ea, eb, target)
    if steps is not None:
        return steps
    # provenance reconstruction can fail on rich graphs; fall back to search. The
    # e-graph linked the classes, so a chain exists — but it may need a reverse
    # (bidirectional) step, so search both directions. Every step is re-checked by
    # robust.recheck_proof before it is trusted as a certificate.
    from .hints import shortest_path
    return shortest_path(source, target, rules, max_depth=max(bound, 12),
                         bidirectional=True, assumptions=assumptions)


def _path_valid(term: MathNode, path) -> bool:
    node = term
    for i in path:
        if i >= len(node.kids):
            return False
        node = node.kids[i]
    return True


def replay_explanation(eg: ProofEGraph, source: MathNode, ea: int, eb: int,
                       target: MathNode) -> list[ProofStep] | None:
    """Turn an e-graph explanation between ``ea`` and ``eb`` into concrete steps.

    Replays the provenance instructions from ``source``, skipping no-op and
    stale-path artifacts of redundant provenance traversal.  Returns ``None``
    (rather than raising) if the reconstructed chain does not reach ``target`` --
    the caller then falls back to a reliable search.
    """
    instrs = eg.explain(ea, eb)
    if instrs is None:
        return None
    steps: list[ProofStep] = []
    term = source
    for rule_id, forward, path, dst in instrs:
        if not _path_valid(term, path):
            continue  # stale path from rich provenance -- skip the artifact
        prev = term
        term = term.replace(path, eg.term_of[dst])
        if term == prev:
            continue  # no-op artifact
        steps.append(ProofStep(rule_id, forward, path, term))
    return steps if term == target else None
