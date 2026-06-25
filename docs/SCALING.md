# Scaling

How far this implementation goes, what the complexity classes are, and where the
wall is. All numbers below are from `bench.py` (free-threaded CPython 3.15t,
Apple Silicon); re-run it to reproduce.

## The one-sentence version

There are **two regimes**, set entirely by whether the active rules *expand*
terms (distributivity, associativity, commutativity) or only *shrink* them.
Equivalence (the grading decision) is cheap; **proof search and saturation are
worst-case exponential**, and the exponential is inherent to equality saturation,
not to this code.

## The underlying problem

Term equivalence modulo a rewrite theory is **undecidable in general** (the word
problem). Our arithmetic theory is decidable, but the two operations we actually
run are both hard in the worst case:

- **Shortest proof / reachability** (BFS): branching `b ≈ O(n·R)`, so `O(b^d)`
  states for proof depth `d` — exponential in depth.
- **Equality saturation** (egg / egglog oracle): the e-graph can grow
  **exponentially in the iteration count** under AC + distributivity; e-matching
  is NP-hard in general.

Only the *decision* "are these equal?" is easy: compare union-find roots,
near-`O(1)`, robust regardless of graph size.

## Per-component complexity

| Component | Complexity | Scales with |
|---|---|---|
| `match`, `evaluate`, `distance` | `O(n)` | term size — trivial |
| `find_counterexample` (disprove) | `O(trials · n)` | polynomial — the robust one |
| `audit_rule` | `O(R · trials · p)` | linear in rules |
| `shortest_path` (bfs) | `O(b^d)`, `b ≈ n·R` | **exponential in proof depth** |
| egglog / egg saturation | `O(bound · E²·R)`, `E` ↑ exp. in `bound` | **exponential in saturation radius** |

The `E²` factor is *this* implementation's naive `rebuild` (recompute to
fixpoint) and un-indexed e-matching (scan all e-nodes × all rules); egg's Rust
core does both near-linearly.

## Measured: the benign regime (shrink-only rules)

`bench.py` family A — a ladder `((..(x+0)+0..)+0) == x`, single rule:

```
   k  nodes   bfs(s)   egg(s) oracle(s) disprove(s)
  32     65    0.004    0.001     0.003      0.0097
  64    129    0.034    0.011     0.006      0.0204
 128    257    0.277    0.018     0.014      0.0402
```

A 257-node term with a 128-step proof proves in <0.3 s. BFS grows ~cubically in
depth; egg/oracle/disprove stay near-linear. **Thousands of nodes and proofs
dozens deep are fine** here.

## Measured: the hostile regime (AC + distributivity)

`bench.py` family B — raw saturation of the full catalogue, no early-stop, on
nested products of sums:

```
            term  iters  e-nodes  time(s)
       2 factors      8      100    0.012     <- plateaus, harmless
       3 factors      4      885    0.023
       3 factors      6    13091    1.224
       3 factors      8    20332   32.876     <- the cliff
```

**Three nested distributable products is the wall.** Distribution × commutativity
is super-exponential; the e-graph *size*, not the proof, is what kills you. The
binding constraint is the number of distributable sub-products (~2–3), not raw
node count.

## Measured: rule count is the easy axis

`bench.py` family C — duplicated catalogue, fixed term, 3 iterations:

```
     R  directed  time(s)
    22        30    0.007
   176       240    0.078
   352       480    0.156
```

Per-step cost is **linear** in the rule count — hundreds of rules are fine for
the machinery. The catch is *kind*, not count: every **expanding / bidirectional**
rule (distributivity, associativity, `sub → add+neg`) multiplies the saturation
blow-up base. A dozen directed rules + a couple of AC rules is the sweet spot;
many expanding rules make saturation unusable regardless of `R`.

## Concrete ceilings

- **Term size:** benign regime → thousands of nodes. With distributivity live,
  the limit is ~2–3 distributable sub-products, *not* node count.
- **Proof depth:** BFS is comfortable to depth ~15–20 with low branching,
  exponential beyond. The e-graph backends find **short, wide** proofs (bounded
  saturation radius, ship `bound=5`), not deep ones.
- **Rules:** hundreds for the engine (linear per step); the real limit is how
  many *expanding* rules you add.

## What keeps it usable, and what would push it further

Already in place: **early-stop saturation** (stop the moment source meets target
— so grading a student's answer a few rewrites from the goal stays in
milliseconds regardless of catalogue size), **`bound=5`**, **landmark-guided
search** (`reference.py` decomposes a global search into bounded local hops), and
**per-exercise precomputation** (saturate once, grade many).

Engineering headroom before the theory wall: a **worklist `rebuild`** (near-linear
instead of `O(E²)`) and an **e-matching index** would reclaim roughly **1–2
orders of magnitude** — e.g. the 20k-node case Rust egglog does in well under a
second. Beyond that the exponential is fundamental to equality saturation; the
mitigations are bounds, early-stop, landmarks, and AC-aware matching, never
removal.

**Bottom line:** sized for "small classroom expressions a handful of steps from
the goal," it is milliseconds and effectively unbounded in rule count. It is not
a general CAS — deep distribution, large polynomial expansion, or proofs >~20
steps are out of reach, and that is a property of the method, not just this
prototype.
