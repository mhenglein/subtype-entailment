"""Independent checks for the exact top-free regular-closure foundation."""

from __future__ import annotations

import json
from pathlib import Path

from topfree_bridge import (
    BottomDenial,
    NormalizedSystem,
    ProductLower,
    ProductUpper,
    ReachablePathSets,
    VariableLeq,
    canonical_countermodel,
    constraint_errors,
    finite_reachable_prefixes,
    forced_root_closure,
    is_satisfiable,
)


def assert_nfa_matches_bounded_closure() -> int:
    """Compare exact-NFA membership with a bounded direct closure.

    The finite comparison is a consistency check only.  The implementation's
    decisions use the exact regular NFA, rather than this depth-limited set.
    """
    systems = [
        NormalizedSystem(
            (
                ProductLower("a", "b", "a"),
                ProductUpper("a", "c", "d"),
                VariableLeq("d", "b"),
            )
        ),
        NormalizedSystem(
            (
                ProductLower("x", "y", "z"),
                ProductUpper("z", "x", "y"),
                VariableLeq("x", "z"),
            )
        ),
    ]
    checks = 0
    for system in systems:
        seeds = [(state, "") for state in sorted(system.forced_roots, key=repr)]
        closure = forced_root_closure(system)
        # The direct diagnostic closure bounds *intermediate* stack height,
        # which can exceed the queried word length after push/pop detours.
        # Keep the comparison words at length <= 8 but allow height 16.
        finite = finite_reachable_prefixes(system, seeds, 16)
        for state in sorted(system.states, key=repr):
            for length in range(9):
                for number in range(1 << length):
                    word = format(number, f"0{length}b") if length else ""
                    expected = (state, word) in finite
                    actual = closure.contains(state, word)
                    if expected != actual:
                        raise AssertionError(
                            f"NFA mismatch for {state!r}, {word!r}: {expected} != {actual}"
                        )
                    checks += 1
    return checks


def check_c0_countermodel() -> None:
    """Reproduce the memo's one-constraint infinite countermodel."""
    system = NormalizedSystem((ProductLower("alpha", "beta", "alpha"),))
    assert is_satisfiable(system)
    result = canonical_countermodel(system, "beta", "alpha", "10")
    assert result.status == "YES", (result.status, result.reason, result.errors)
    assert result.model is not None
    assert result.model.contains("beta", "10")
    assert not result.model.contains("alpha", "10")
    assert result.model.prefix_closed()
    assert not result.model.as_finite_automaton_data()["nfa_states"] == 0

    rejected = canonical_countermodel(system, "beta", "alpha", "1")
    assert rejected.status == "REJECTED_PATH"


def check_stack_and_identifier_edges() -> None:
    """Exercise mixed hashable IDs, empty pops, pushes followed by pops, and eps."""
    mixed = NormalizedSystem(
        (
            ProductLower("left", 7, ("target",)),
            VariableLeq(("target",), 7),
        )
    )
    mixed_closure = forced_root_closure(mixed)
    assert mixed_closure.contains(("target",), "")
    assert mixed_closure.contains(7, "")
    assert constraint_errors(mixed, mixed_closure) == []

    pop_only = NormalizedSystem((ProductUpper("src", "left", "right"),))
    pop_closure = ReachablePathSets(pop_only, (("src", ""),))
    assert pop_closure.contains("src", "")
    assert not pop_closure.contains("left", "")
    assert not pop_closure.contains("right", "")

    push_pop = NormalizedSystem(
        (
            ProductLower("a", "b", "p"),
            ProductUpper("p", "a", "b"),
        )
    )
    push_pop_closure = ReachablePathSets(push_pop, (("a", ""), ("p", "")))
    assert push_pop_closure.contains("p", "0")
    assert push_pop_closure.contains("a", "")
    assert constraint_errors(push_pop, push_pop_closure) == []

    epsilon = NormalizedSystem((VariableLeq("eps-source", "eps-target"),))
    epsilon_closure = ReachablePathSets(epsilon, (("eps-source", ""),))
    assert epsilon_closure.contains("eps-target", "")


def check_unsatisfiable_forced_root() -> None:
    system = NormalizedSystem(
        (
            ProductLower("alpha", "beta", "gamma"),
            BottomDenial("gamma"),
        )
    )
    assert not is_satisfiable(system)
    result = canonical_countermodel(system, "alpha", "beta", "")
    assert result.status == "UNSAT"
    assert "unsatisfiable" in result.reason


def check_upper_and_epsilon_constraints() -> None:
    """Check that quotient and epsilon inclusions are validated exactly."""
    system = NormalizedSystem(
        (
            ProductLower("a", "b", "p"),
            ProductUpper("p", "a", "b"),
            VariableLeq("a", "p"),
        )
    )
    assert is_satisfiable(system)
    closure = forced_root_closure(system)
    # The least solution is enough to test exact normalization checks.
    assert constraint_errors(system, closure) == []
    assert closure.prefix_closed()


def main() -> None:
    bounded_checks = assert_nfa_matches_bounded_closure()
    check_c0_countermodel()
    check_unsatisfiable_forced_root()
    check_upper_and_epsilon_constraints()
    check_stack_and_identifier_edges()
    result = {
        "status": "PASS",
        "scope": "exact regular post-closure and normalized constraint validation",
        "bounded_diagnostic_checks": bounded_checks,
        "c0_countermodel": "validated",
        "forced_root_denial": "validated",
        "upper_and_epsilon_constraints": "validated",
        "status_contract": "YES/UNSAT/REJECTED_PATH",
        "mixed_hashable_ids": "validated",
        "empty_pop_push_pop_epsilon": "validated",
        "global_claim": "not a decision procedure for Problem 1.7",
    }
    output = Path(__file__).resolve().parents[1] / "results" / "topfree-bridge.json"
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
