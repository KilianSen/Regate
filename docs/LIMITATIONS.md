# Limitations

An honest account of where this prototype stops. The useful distinction is
between **deliberate scope** (chosen, defensible for a thesis baseline),
**prototype immaturity** (fixable with engineering), and **fundamental method
limits** (inherent to equality saturation / proof search). Each item is tagged.

## 1. Soundness guarantees are empirical, not formal  *(immaturity)*

- `check_rules.py` and `find_counterexample` are **random testing over a fixed
  rational pool** (`{-3..7}`), not proof. A rule unsound only at, say, `x = 1/7`
  or `x = 1000`, or only for a particular *structure*, would pass. They catch the
  obvious failures (division by zero, via definedness-preserving equality) but
  guarantee nothing.
- So the strongest honest claim is "no counterexample found," never "sound." The
  real fix — proving the rule library once in **Lean/Isabelle** — is documented
  but not built. (See the `Leanregate` companion if/when that lands.)
- Guards discharged by **student-declared assumptions** (`x ≠ 0`) are *trusted*,
  not verified against context. There is no interval/sign analysis, so a student
  could declare a false assumption and the validator would accept it.

## 2. Proving is incomplete — both ways  *(method + immaturity)*

- **BFS** is forward-only and depth-capped (default 8): it misses uphill /
  symmetric goals and any deep proof.
- **egg / oracle** use bounded saturation (`bound=5`) because AC + distributivity
  has no finite fixpoint and the e-graph explodes. Equivalences needing more
  rewriting are reported as "not proven."
- Net: there are genuinely-equal expressions the system cannot certify (surfaced
  honestly as `UNKNOWN`) and genuinely-unequal ones it cannot disprove (if the
  witness is outside the pool). It is correct when it commits, but it **abstains
  more than a production grader could tolerate**, and `UNKNOWN` needs a
  human-review fallback that does not exist yet.

## 3. The egg backend is our reimplementation  *(immaturity)*

- ~450 LOC of proof-producing congruence closure — not egg itself, not verified.
  Found-and-patched issues (no-op artifacts, the rich-graph replay crash) suggest
  there are more on untested inputs; `recheck_proof` catches *wrong* proofs and
  the fallback contains *crashes*, but neither is a correctness proof.
- **Proofs are not minimal** (egg's aren't either; the FMCAD-2022 minimization
  pass is omitted). Early-stop makes the proof depend on saturation order.
- **Flat-proof reconstruction from a rich (precomputed) graph is fragile** — e-node
  identity is lost through `find`, and provenance paths go stale. *Contained* by
  graceful fallback to a fresh search, not fixed at the root. True O(1) proofs off
  the precomputed graph would need an e-graph identity/provenance rewrite.

## 4. Expressiveness is school-algebra only  *(deliberate scope)*

- **No binders** (∀ ∃ λ Σ ∫) → no alpha-equivalence, no calculus or quantified
  logic. Retrofitting needs de Bruijn / nominal representation *up front*.
- Numbers are integers/rationals only — no reals, irrationals, or symbolic
  constants. `√(x²) = |x|` cannot even be *written* (no `sqrt`/`abs` blocks). No
  exponents, logs, trig.
- 22 rules. AC equality is rule-driven, not built into matching, so it is
  sensitive to term ordering unless the right rules fire.

## 5. Not integrated with Artemis  *(deliberate scope / deployment gap)*

- Standalone **Python** prototype on a **hand-patched egglog wheel** running on a
  CPython **3.15 beta** free-threaded build — not a deployable runtime, and not
  validated for the concurrency that build exists for.
- Artemis's MS1/MS2 are **Java / Angular**. The "single shared rule source" here
  is shared between our *two Python engines*, **not** with Artemis's real Java
  server and TS client — so the cross-tier consistency the thesis emphasises is
  not achieved across the actual client/server. Deploying needs a Python
  microservice or a port.
- No REST surface, persistence, auth, i18n, or DoS hardening beyond `max_nodes` /
  `bound` caps.

## 6. Grading & pedagogy rest on heuristics  *(method)*

- Partial credit (`MathNodeDistance`, `progress`) is a heuristic, explicitly not
  rigorous.
- `N_min` / "elegance" assumes shortest-proof = best, which is pedagogically
  debatable. Multi-step hints are *minimal-step*; the "clear the +0 first"
  ordering is a hand-picked filter, not a learned model.
- The semantic disprover does not handle `eq`-blocks (returns undefined), so
  **equation-mode grading is weaker** than transformation-mode.

## 7. Testing breadth  *(immaturity)*

39 tests, concentrated on the single Appendix B example plus a handful of cases.
No property-based testing across many exercises — which is exactly where the egg
backend's untested paths would surface.

---

**The through-line:** within its scope it is *sound when it commits* (proof +
re-check + disproof, never a bare boolean), but it **abstains often, is not
formally verified, does not scale past small expressions, and is not wired into
the real platform.** Future-work value order: **(1) Lean-verified rule library →
(2) completeness / better bounds → (3) Artemis integration.**
