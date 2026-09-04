"""Checks for the actual subtype-derived summary and border bridge."""

from __future__ import annotations

import json
from pathlib import Path

from border_lab import witness, words
from summary_bridge import (
    NormalizedSystem,
    ProductLower,
    ProductUpper,
    VariableLeq,
    build_pop_summary,
    build_summary_bridge,
    is_satisfiable,
    pop_contains,
    summary_diagnostics,
)
from topfree_bridge import BottomDenial, PDSRule, canonical_countermodel


def check_pop_empty_and_balanced_edges() -> None:
    """Check empty-stack pops and push/pop summary cancellation."""
    pop_only = NormalizedSystem((ProductUpper("src", "left", "right"),))
    summary = build_pop_summary(pop_only.rules, ("src", "left", "right"))
    assert not pop_contains(summary, "src", "left", "")
    assert pop_contains(summary, "src", "left", "0")
    assert pop_contains(summary, "src", "right", "1")

    generator_rules = (
        rule
        for rule in (
            PDSRule("start", "mid", "push", "0"),
            PDSRule("mid", "finish", "pop", "0"),
        )
    )
    generator_summary = build_pop_summary(generator_rules, ("start", "mid", "finish"))
    assert pop_contains(generator_summary, "start", "finish", "")

    push_pop = NormalizedSystem(
        (
            ProductLower("a", "b", "p"),
            ProductUpper("p", "a", "b"),
        )
    )
    reversed_summary = build_pop_summary(
        tuple(
            PDSRule(rule.target, rule.source,
                    {"push": "pop", "pop": "push", "eps": "eps"}[rule.operation],
                    rule.letter)
            for rule in push_pop.rules
        ),
        ("a", "b", "p"),
    )
    # A reverse pop consumes the one visible stack symbol before reaching a.
    assert pop_contains(reversed_summary, "p", "a", "0")


def check_subtype_derived_witnesses(max_length: int = 6) -> int:
    """Compare summary BorderAvoid witnesses with canonical models."""
    cases = [
        (
            "c0",
            NormalizedSystem((ProductLower("alpha", "beta", "alpha"),)),
            "beta",
            "alpha",
        ),
        ("empty-system", NormalizedSystem(()), "x", "y"),
        (
            "pop",
            NormalizedSystem((ProductUpper("src", "left", "right"),)),
            "src",
            "target",
        ),
        (
            "denial",
            NormalizedSystem(
                (
                    ProductLower("x", "y", "gamma"),
                    BottomDenial("x"),
                )
            ),
            "x",
            "y",
        ),
        (
            "denial-with-residual-stack",
            NormalizedSystem(
                (
                    ProductUpper("seed", "denial", "other"),
                    BottomDenial("denial"),
                )
            ),
            "seed",
            "target",
        ),
        (
            "epsilon",
            NormalizedSystem((VariableLeq("x", "y"),)),
            "x",
            "z",
        ),
    ]
    comparisons = 0
    for name, system, alpha, beta in cases:
        assert is_satisfiable(system), name
        bridge = build_summary_bridge(system, alpha, beta)
        for word in words("01", max_length):
            from_summary = witness(bridge.instance, word)
            canonical = canonical_countermodel(system, alpha, beta, word)
            from_canonical = canonical.status == "YES"
            if from_summary != from_canonical:
                raise AssertionError(
                    f"{name}: mismatch for {word!r}: summary={from_summary}, "
                    f"canonical={canonical.status} ({canonical.reason})"
                )
            comparisons += 1
    return comparisons


def check_unsat_and_absent_query_variables() -> None:
    """Reject unsatisfiable systems while accepting unconstrained query IDs."""
    unsatisfiable = NormalizedSystem(
        (
            ProductLower("a", "b", "forced"),
            BottomDenial("forced"),
        )
    )
    try:
        build_summary_bridge(unsatisfiable, "a", "b")
    except ValueError as error:
        assert "unsatisfiable" in str(error)
    else:
        raise AssertionError("unsatisfiable bridge construction was accepted")

    unconstrained = NormalizedSystem(())
    bridge = build_summary_bridge(unconstrained, "missing-alpha", "missing-beta")
    assert bridge.states == ("missing-alpha", "missing-beta")
    assert bridge.instance.run("") == (0,)


def check_actual_flag_relation() -> None:
    """Check that each generated flag is exactly a summary-set intersection."""
    system = NormalizedSystem((ProductLower("alpha", "beta", "alpha"),))
    bridge = build_summary_bridge(system, "beta", "alpha")
    for left, left_class in enumerate(bridge.classes):
        for right, right_class in enumerate(bridge.classes):
            expected = bool(left_class.b_states.intersection(right_class.a_states))
            assert bridge.flag(left, right) == expected
    assert any(bridge.classes[state].b_states == frozenset() for state in range(len(bridge.classes)))
    assert any(bridge.classes[state].a_states == frozenset() for state in range(len(bridge.classes)))


def main() -> None:
    check_pop_empty_and_balanced_edges()
    check_actual_flag_relation()
    check_unsat_and_absent_query_variables()
    comparisons = check_subtype_derived_witnesses()
    c0 = build_summary_bridge(
        NormalizedSystem((ProductLower("alpha", "beta", "alpha"),)),
        "beta",
        "alpha",
    )
    result = {
        "status": "PASS",
        "scope": "actual W/Wrev pop summaries, S/F annotations, and witness cross-check",
        "witness_comparisons": comparisons,
        "max_word_length": 6,
        "c0_summary": summary_diagnostics(c0),
        "empty_stack_pop": "validated",
        "push_pop_summary": "validated",
        "generator_rule_input": "validated",
        "actual_flag_relation": "validated",
        "unsat_precondition": "validated",
        "absent_query_variables": "validated",
        "s_annotation": "exact denial predecessor NFA",
        "f_annotation": "exact forced-root endpoint condition",
        "global_claim": "not a decision procedure for Problem 1.7",
    }
    output = Path(__file__).resolve().parents[1] / "results" / "summary-bridge.json"
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
