"""Eggregate's conformance to the unified grading protocol (GRADING_PROTOCOL.md).

`grade(request: dict) -> dict` is the single handler behind both the CLI and HTTP
transports (`server.py`).  It maps the protocol onto the package internals:

  * a submitted *derivation* (`steps`) is checked per-step with the validator
    (sound by construction, Type-A/B);
  * a submitted *final* expression is graded by `decide_equivalence` -- disprove
    first (sound witness), then a re-checked constructive proof, then the oracle;
  * an optional reference supplies guided hints and structural progress.

Everything returns the protocol envelope; `score` may be ``None`` (route to
review) -- the contract's false-negative defence.
"""
from __future__ import annotations

from time import perf_counter

from .audit import audit_catalogue
from .catalogue import BY_ID, CATALOGUE, ruleset_from_json
from .conditions import Assumption
from .model import MathNode, distance, from_json, pretty, to_json
from .hints import greedy_hints, shortest_path
from .reference import guided_hint, progress, reference_from_states
from .robust import (
    EQUAL_NO_CERTIFICATE, PROVEN_EQUAL, PROVEN_UNEQUAL, UNKNOWN,
    decide_equivalence,
)
from .validate import Equation, Move, verify_chain

PROTOCOL = "1.0"
BACKEND = "eggregate"
VERSION = "0.1.0"


class RequestError(ValueError):
    """Malformed request -> HTTP 400 / CLI exit 2."""


def _resolve_rules(ex: dict):
    """Resolve the exercise's ruleset to a (list, id->Rule) pair.

    Priority: an inline ``ruleset`` of full rule *definitions* (instructor-
    authored, travels in the request); else ``rules`` as ids / "ALL" into the
    shipped catalogue (convenience / back-compat).
    """
    if ex.get("ruleset"):
        try:
            rules = ruleset_from_json(ex["ruleset"])
        except (ValueError, KeyError, TypeError) as e:
            raise RequestError(f"invalid ruleset: {e}")
        custom = True
    else:
        spec = ex.get("rules")
        if spec in (None, "ALL"):
            rules = list(CATALOGUE)
        else:
            try:
                rules = [BY_ID[r] for r in spec]
            except KeyError as e:
                raise RequestError(f"unknown rule id {e.args[0]!r}")
        custom = False
    return rules, {r.id: r for r in rules}, custom


def _step_to_json(s) -> dict:
    return {
        "rule": s.rule_id,
        "path": list(s.path),
        "direction": "forward" if getattr(s, "forward", True) else "reverse",
        "state": to_json(s.state),
    }


def _moves_from_steps(steps, by_id, hyps) -> list[Move]:
    """Build Moves. A Type-B (Leibniz) step is in scope only if its equation is
    one of the exercise's given hypotheses -- otherwise a student could substitute
    with a false equation and "prove" anything."""
    moves = []
    for s in steps:
        path = tuple(s.get("path", []))
        if s.get("kind", "A") == "B":
            lhs, rhs = from_json(s["equation"][0]), from_json(s["equation"][1])
            moves.append(Move("B", path, equation=Equation(lhs, rhs), in_scope=(lhs, rhs) in hyps))
        else:
            rid = s["rule"]
            if rid not in by_id:
                raise RequestError(f"unknown rule id {rid!r}")
            moves.append(Move("A", path, rule=by_id[rid],
                              reverse=(s.get("direction") == "reverse")))
    return moves


def _parse_assumptions(ex) -> frozenset:
    """Student/instructor-declared facts that discharge guarded side conditions,
    e.g. {"kind": "nonzero", "value": <MathNode for x>} for "x != 0"."""
    out = set()
    for a in ex.get("assumptions") or []:
        try:
            out.add(Assumption(a["kind"], from_json(a["value"])))
        except (KeyError, TypeError) as e:
            raise RequestError(f"invalid assumption: {e}")
    return frozenset(out)


def _parse_hypotheses(ex) -> set:
    """Given equalities the student may use in Type-B substitutions -> a set of
    (lhs, rhs) MathNode pairs."""
    hyps = set()
    for h in ex.get("hypotheses") or []:
        node = from_json(h)
        if node.op != "eq":
            raise RequestError("each hypothesis must be an equality (eq) expression")
        # Equality is symmetric: a hypothesis may be substituted either way.
        hyps.add((node.slot("left"), node.slot("right")))
        hyps.add((node.slot("right"), node.slot("left")))
    return hyps


def _prove_lemmas(lemmas, by_id, base_hyps, assumptions):
    """Prove the student's auxiliary lemmas (`have L = R := <derivation>`) and add
    each established equality -- in both directions -- to the Type-B scope.

    A lemma is a self-contained sub-derivation from its own ``source`` L; whatever
    it validly reduces to is R, and ``L = R`` becomes available to later lemmas and
    to the main proof. Soundness is preserved: an equality is added only once its
    derivation type-checks (every step valid, guards discharged). Returns
    ``(hyps, error)``; ``error`` is non-None if a lemma fails to derive.
    """
    hyps = set(base_hyps)
    for i, lem in enumerate(lemmas):
        if "source" not in lem:
            return frozenset(hyps), f"lemma {i} has no source"
        start = from_json(lem["source"])
        moves = _moves_from_steps(lem.get("steps", []), by_id, frozenset(hyps))
        report = verify_chain(start, moves, None, assumptions=assumptions)
        if not report.valid:
            bad = len(report.results) - 1
            reason = report.results[bad].reason if report.results else "no valid step"
            return frozenset(hyps), f"lemma {i} step {bad}: {reason}"
        result = report.states[-1]
        hyps.add((start, result))
        hyps.add((result, start))
    return frozenset(hyps), None


def grade(request: dict) -> dict:
    t0 = perf_counter()
    if request.get("protocol", PROTOCOL).split(".")[0] != PROTOCOL.split(".")[0]:
        raise RequestError(f"unsupported protocol {request.get('protocol')!r}")

    ex = request.get("exercise") or {}
    sub = request.get("submission") or {}
    mode = ex.get("mode", "transformation")
    rules, by_id, custom = _resolve_rules(ex)
    opts = ex.get("options") or {}

    # Custom rules are untrusted: optionally audit them for soundness here, so an
    # instructor-authored rule that lies (e.g. x/x->1 without x!=0) is rejected
    # before it can grade anything. (Authoring-time is the better place; this is
    # the per-request safety net.)
    if custom and opts.get("audit_rules"):
        for a in audit_catalogue(rules, trials=opts.get("audit_trials", 400)):
            if not a.sound:
                wit = ", ".join(f"{k}={v}" for k, v in a.counterexample.items())
                raise RequestError(f"unsound rule {a.rule_id!r}: counterexample {wit}")

    if "source" not in ex:
        raise RequestError("exercise.source is required")
    source = from_json(ex["source"])
    target = from_json(ex["target"]) if ex.get("target") is not None else None
    if mode == "transformation" and target is None:
        raise RequestError("transformation mode requires exercise.target")
    if sub.get("final") is None and not sub.get("steps"):
        raise RequestError("submission must have a final expression or steps")

    ref = None
    if ex.get("reference"):
        ref = reference_from_states([from_json(s) for s in ex["reference"]])

    assumptions = _parse_assumptions(ex)
    hyps = _parse_hypotheses(ex)

    # Prove any auxiliary lemmas first; each established equality joins the Type-B
    # scope for the main derivation (a derived equality, reusable later).
    lemma_error = None
    if sub.get("lemmas"):
        hyps, lemma_error = _prove_lemmas(sub["lemmas"], by_id, hyps, assumptions)

    if lemma_error:
        resp = {"outcome": "invalid_derivation", "score": 0, "certified": False,
                "proof": None, "witness": None, "steps": None, "hint": None,
                "feedback": f"invalid lemma — {lemma_error}", "meta": {}}
    else:
        resp = _grade_core(source, target, rules, by_id, sub, opts, ref, assumptions, hyps)
    resp.update(protocol=PROTOCOL, backend=BACKEND, backend_version=VERSION)
    resp.setdefault("meta", {})["ms"] = round((perf_counter() - t0) * 1e3, 1)
    return resp


def _invalid(steps_out, idx, reason) -> dict:
    return {"outcome": "invalid_derivation", "score": 0, "certified": False,
            "proof": None, "witness": None, "steps": steps_out, "hint": None,
            "feedback": f"step {idx} invalid: {reason}"}


def _grade_core(source, target, rules, by_id, sub, opts, ref, assumptions=frozenset(), hyps=frozenset()) -> dict:
    steps_out = None
    final = None

    # 1) a submitted derivation: each step must be a valid rule application AND
    #    its claimed result must match what the rule actually produces (the
    #    thesis's RewriteChainGrader check (iii)). Guarded steps are discharged
    #    against the declared `assumptions`; Type-B steps must use a hypothesis.
    if sub.get("steps"):
        steps_in = sub["steps"]
        moves = _moves_from_steps(steps_in, by_id, hyps)
        report = verify_chain(source, moves, target, assumptions=assumptions)
        steps_out = [{"index": i, "status": r.status, "reason": r.reason}
                     for i, r in enumerate(report.results)]
        if not report.valid:
            return _invalid(steps_out, len(report.results) - 1, report.results[-1].reason)
        recomputed = report.states[1:]
        for i, st in enumerate(steps_in):
            if st.get("result") is not None and from_json(st["result"]) != recomputed[i]:
                steps_out[i].update(status="invalid",
                                    reason="claimed result does not match the rule output")
                return _invalid(steps_out, i, "claimed result does not match the rule output")
        if report.reached_goal:                       # reached the target *form*
            proof = [{"rule": m.rule.id if m.rule else "subst", "path": list(m.path),
                      "direction": "reverse" if m.reverse else "forward", "state": to_json(s)}
                     for m, s in zip(moves, recomputed)]
            return {"outcome": PROVEN_EQUAL, "score": 100, "certified": True,
                    "proof": proof, "witness": None, "steps": steps_out, "hint": None,
                    "feedback": "Valid derivation reaching the goal.", "meta": {}}
        final = report.states[-1]                      # valid but unfinished

    if final is None:
        final = from_json(sub["final"])
    if target is None:                                 # equation mode
        return _grade_equation(source, final, rules, steps_out)

    resp = _grade_final(source, final, target, rules)
    resp["steps"] = steps_out
    # Hint toward the goal when the answer is not yet full marks. A reference
    # derivation steers the hint onto the intended route (§B.4); without one we
    # still offer the shortest directed next move.
    if opts.get("want_hint") and resp["score"] != 100:
        if ref is not None:
            h = guided_hint(final, ref, rules)
            if h.step is not None:
                resp["hint"] = {"rule": h.step.rule_id, "path": list(h.step.path),
                                "direction": "forward", "remaining": h.remaining}
        if resp.get("hint") is None:
            resp["hint"] = _hint_toward(final, target, rules)
    if ref is not None:
        resp.setdefault("meta", {})["progress"] = round(progress(final, ref), 3)
    return resp


def _hint_toward(state, target, rules) -> dict | None:
    """A next-move hint toward ``target`` without an instructor reference.

    Prefers a step on a *shortest* directed path (so ``remaining`` is the true
    minimal distance); falls back to the greedy one-ply move when the goal is not
    reachable within the search bound.
    """
    plan = shortest_path(state, target, rules)
    if plan:
        s = plan[0]
        return {"rule": s.rule_id, "path": list(s.path), "direction": "forward",
                "remaining": len(plan)}
    greedy = greedy_hints(state, target, rules, k=1)
    if greedy:
        g = greedy[0]
        return {"rule": g.rule_id, "path": list(g.path), "direction": "forward",
                "remaining": None}
    return None


def _grade_equation(source, final, rules, steps_out) -> dict:
    """Equation mode: the submission proves an equation by showing its two sides
    are equivalent (e.g. reducing ``x + 0 = x`` to ``x = x``).

    Success is decided on the *final* equation's sides, so a student may either
    submit a derivation that reaches a reflexive ``a = a`` or a final equation
    whose sides this backend can prove equivalent under the ruleset.
    """
    base = {"proof": None, "witness": None, "steps": steps_out, "hint": None, "meta": {}}
    if final.op != "eq":
        return {**base, "outcome": "invalid_derivation", "score": 0, "certified": False,
                "feedback": "equation mode expects an equality (eq) expression."}
    lhs, rhs = final.slot("left"), final.slot("right")
    if lhs == rhs:
        return {**base, "outcome": PROVEN_EQUAL, "score": 100, "certified": True,
                "proof": [], "feedback": "Both sides are identical — the equation holds."}
    v = decide_equivalence(lhs, rhs, rules)
    if v.outcome == PROVEN_UNEQUAL:
        return {**base, "outcome": PROVEN_UNEQUAL, "score": 0, "certified": True,
                "witness": {k: str(val) for k, val in v.witness.items()},
                "feedback": "The two sides are not equal (counterexample found)."}
    if v.outcome == PROVEN_EQUAL:
        return {**base, "outcome": PROVEN_EQUAL, "score": 100, "certified": True,
                "proof": [_step_to_json(s) for s in (v.proof or [])],
                "feedback": "The two sides are equivalent — the equation holds."}
    if v.outcome == EQUAL_NO_CERTIFICATE:
        return {**base, "outcome": EQUAL_NO_CERTIFICATE, "score": None, "certified": False,
                "feedback": "Believed to hold but no checkable proof was produced; review."}
    return {**base, "outcome": UNKNOWN, "score": None, "certified": False,
            "feedback": "Could not prove or disprove the equation within budget; review."}


def _grade_final(source, final, target, rules) -> dict:
    """Transformation grade for a final expression.

    Reaching the target *form* is full marks; a value-equivalent but unsimplified
    answer earns partial credit (the thesis's distance formula) -- the e-graph
    distinguishes "wrong" from "right value, keep going"; not equivalent is zero
    with a numeric witness.
    """
    base = {"proof": None, "witness": None, "steps": None, "hint": None, "meta": {}}
    if final == target:
        return {**base, "outcome": PROVEN_EQUAL, "score": 100, "certified": True,
                "proof": [], "feedback": "Reached the target form."}
    v = decide_equivalence(final, target, rules)
    if v.outcome == PROVEN_UNEQUAL:
        return {**base, "outcome": PROVEN_UNEQUAL, "score": 0, "certified": True,
                "witness": {k: str(val) for k, val in v.witness.items()},
                "feedback": "Not equivalent to the goal (counterexample found)."}
    if v.outcome == PROVEN_EQUAL:
        d0 = max(1, distance(source, target))
        score = max(0, min(99, int((1 - distance(final, target) / d0) * 100)))
        return {**base, "outcome": PROVEN_EQUAL, "score": score, "certified": True,
                "proof": [_step_to_json(s) for s in (v.proof or [])],
                "feedback": "Equivalent to the goal but not yet in the required form; "
                            "keep simplifying."}
    if v.outcome == EQUAL_NO_CERTIFICATE:
        return {**base, "outcome": EQUAL_NO_CERTIFICATE, "score": None, "certified": False,
                "feedback": "Believed equivalent but no checkable proof was produced; review."}
    return {**base, "outcome": UNKNOWN, "score": None, "certified": False,
            "feedback": "Could not prove or disprove within budget; review."}
