#!/usr/bin/env python3
"""Regression for exact finite interface facts used by middle erasure."""

import json
from pathlib import Path

from regular_middle_interface import interface_summary

# Middle DFA for (0^+ 11)*. State 0 is both start and accepting.
MIDDLE = (
    (1, -1),
    (1, 2),
    (-1, 0),
)

# Six-state benchmark original DFA.
ORIGINAL = (
    (1, 2),
    (1, 2),
    (3, -1),
    (3, 4),
    (5, 2),
    (-1, -1),
)


def main():
    good = interface_summary(MIDDLE, 0, {0}, ORIGINAL, 2)
    assert good == {
        "boundary_state": 2,
        "all_words_return_boundary": True,
        "boundary_counterexample": None,
        "common_nonempty_prefix": "0",
        "epsilon_in_middle": True,
    }

    # Negative control 1: asking for the wrong original boundary state exposes
    # a complete accepted middle counterexample.
    wrong_boundary = interface_summary(MIDDLE, 0, {0}, ORIGINAL, 3)
    assert not wrong_boundary["all_words_return_boundary"]
    assert wrong_boundary["boundary_counterexample"] is not None

    # Negative control 2: a regular middle with both 0 and 1 as one-letter
    # accepted words has no forced first symbol.
    branching = (
        (1, 1),
        (-1, -1),
    )
    branch_summary = interface_summary(branching, 0, {1}, ORIGINAL, 0)
    assert branch_summary["common_nonempty_prefix"] == ""

    result = {
        "status": "PASS",
        "benchmark_interface": good,
        "negative_controls": {
            "wrong_boundary_counterexample": wrong_boundary["boundary_counterexample"],
            "branching_common_prefix": branch_summary["common_nonempty_prefix"],
        },
        "scope": (
            "Exact finite interface analysis only. This does not establish a complete "
            "middle-erasure search or unrestricted BorderAvoid decision."
        ),
    }
    out = Path(__file__).resolve().parents[1] / "results" / "regular-middle-interface.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
