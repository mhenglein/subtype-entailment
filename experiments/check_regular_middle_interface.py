#!/usr/bin/env python3
"""Regression for exact finite interface facts used by middle erasure."""

import json
from pathlib import Path

from regular_middle_interface import interface_summary, scc_return_interfaces

MIDDLE = (
    (1, -1),
    (1, 2),
    (-1, 0),
)

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

    discovered = scc_return_interfaces(ORIGINAL)
    target = [row for row in discovered
              if tuple(row["component"]) == (2, 3, 4) and row["boundary_state"] == 2]
    assert len(target) == 1
    assert target[0]["common_nonempty_prefix"] == "0"

    wrong_boundary = interface_summary(MIDDLE, 0, {0}, ORIGINAL, 3)
    assert not wrong_boundary["all_words_return_boundary"]
    assert wrong_boundary["boundary_counterexample"] == "011"

    branching = ((1, 1), (-1, -1))
    branch_summary = interface_summary(branching, 0, {1}, ORIGINAL, 0)
    assert branch_summary["common_nonempty_prefix"] == ""

    rows = [
        {
            "component": list(row["component"]),
            "boundary_state": row["boundary_state"],
            "common_nonempty_prefix": row["common_nonempty_prefix"],
        }
        for row in discovered
    ]
    result = {
        "status": "PASS",
        "benchmark_interface": good,
        "discovered_scc_return_interfaces": rows,
        "negative_controls": {
            "wrong_boundary_counterexample": wrong_boundary["boundary_counterexample"],
            "branching_common_prefix": branch_summary["common_nonempty_prefix"],
        },
        "scope": (
            "Exact finite interface/SCC-return analysis only. A comparison selector "
            "is still required before any discovered middle may be erased soundly."
        ),
    }
    out = Path(__file__).resolve().parents[1] / "results" / "regular-middle-interface.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
