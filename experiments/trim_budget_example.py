"""Trim a preserved witness to refute the candidate bound B <= max(0,k-2).

Restriction removes possible runs. A surviving word keeps its state flags
and sufficient budgets, so restriction cannot lower the minimum budget.
The finite search also independently checks every lower budget on the
trimmed instance. This is an abstract BorderAvoid example, not a subtype
realization or an asymptotic lower bound.
"""

import json
from pathlib import Path

from border_lab import Instance, border_witness, sufficient, witness, words
from boundary_slices import final_slices
from search_budgets import decode_instance, encode_instance, search_budget


ROOT = Path(__file__).resolve().parents[1]


def restrict_to_states(instance, retained):
    old_states = sorted(set(retained))
    index = {q: i for i, q in enumerate(old_states)}
    return Instance(
        tuple(tuple(index.get(r, -1) for r in instance.delta[q]) for q in old_states),
        frozenset(index[q] for q in instance.final if q in index),
        frozenset((index[q], index[r]) for q, r in instance.flags
                  if q in index and r in index),
        frozenset(index[q] for q in instance.bad if q in index),
        index[instance.start], instance.alphabet,
    ), old_states


def main():
    source = json.loads((ROOT / "results/shortest-witnesses.json").read_text())
    row = next(row for row in source["targeted"]["rows"] if row["attempt"] == 3)
    original = decode_instance(row["instance"])
    preserved = row["budget_search"]["word"]
    trimmed, old_states = restrict_to_states(original, original.run(preserved))
    maximum, cap = 5, 200000
    result = search_budget(trimmed, maximum, cap)
    assert result["status"] == "EXACT", result
    assert result["budget"] == 5 and len(trimmed.delta) == 6
    assert result["budget"] > max(0, len(trimmed.delta) - 2)
    assert witness(trimmed, preserved) and border_witness(trimmed, preserved)
    assert sufficient(trimmed, preserved, 5, 0)

    comparisons = 0
    shortest = None
    for word in words("01", len(preserved)):
        ours = witness(trimmed, word)
        assert ours == border_witness(trimmed, word)
        if ours:
            assert witness(original, word)
            if shortest is None:
                shortest = word
        comparisons += 1
    assert shortest is not None
    boundary = []
    for part in final_slices(trimmed):
        budget = ({"status": "EMPTY", "reason": "complete boundary graph exhausted"}
                  if part.shortest is None else search_budget(part.relaxed, maximum, cap))
        assert budget["status"] in {"EMPTY", "EXACT"}, budget
        boundary.append({"final": part.final, "shortest_word": part.shortest,
                         "budget": budget})
    boundary_budget = min(part["budget"]["budget"] for part in boundary
                          if part["budget"]["status"] == "EXACT")
    assert boundary_budget == 1
    output = {
        "status": "PASS",
        "source": {"path": "results/shortest-witnesses.json", "targeted_attempt": 3},
        "original_states": len(original.delta),
        "retained_old_states": old_states,
        "instance": encode_instance(trimmed),
        "search_limits": {"max_budget": maximum, "state_cap": cap},
        "budget_search": result,
        "shortest_word": shortest,
        "shortest_length": len(shortest),
        "word_comparisons": comparisons,
        "max_word_length": len(preserved),
        "boundary_slices": boundary,
        "full_boundary_budget": boundary_budget,
        "proper_border_budget_increase": result["budget"] - boundary_budget,
        "refuted_candidate": "B(I) <= max(0, number_of_states - 2) for all abstract instances",
        "scope": "finite computational counterexample; no asymptotic or SEP-realizability claim",
    }
    (ROOT / "results/trimmed-budget.json").write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
