"""Reproduce the boundary decomposition, certificates, and corrected baselines."""

import json
from collections import Counter
from pathlib import Path

from border_lab import necessary, sufficient, witness, words
from boundary_slices import (boundary_accepts, final_slices,
                             regularity_certificate, two_state_decision)
from check_context_cuts import all_two_state_instances, generated_instances
from search_budgets import decode_instance, search_budget


ROOT = Path(__file__).resolve().parents[1]


def check_instance(instance, maximum, counts, is_small=False):
    slices = final_slices(instance)
    certificate = regularity_certificate(instance, slices)
    counts["regularity_" + certificate["status"]] += 1
    if certificate["status"] == "YES":
        assert witness(instance, certificate["word"])
        assert len(certificate["word"]) < len(instance.delta)
    saw_witness = False
    for word in words(instance.alphabet, maximum):
        actual = witness(instance, word)
        boundary = boundary_accepts(slices, word)
        assert boundary == necessary(instance, word, 0, 0)
        assert not actual or boundary
        if certificate["status"] != "UNKNOWN":
            assert actual == boundary
        saw_witness |= actual
        counts["words"] += 1
    if is_small:
        decision = two_state_decision(instance, slices)
        assert (decision["status"] == "YES") == saw_witness
        counts["two_state_" + decision["status"]] += 1
        if decision["status"] == "YES":
            word = decision["word"]
            assert len(word) <= 1 and witness(instance, word)
            assert sufficient(instance, word, 0, 0)
            counts["two_state_shortest_length_" + str(len(word))] += 1


def budget_diagnostics():
    stored = json.loads((ROOT / "results/budget-search.json").read_text())
    output = []
    for row in stored["results"]["top_growth_over_no_flag"]:
        instance = decode_instance(row["instance"])
        original_budget = row["flagged"]["budget"]
        components = []
        for part in final_slices(instance):
            if part.shortest is None:
                result = {"status": "EMPTY", "reason": "finite graph exhausted"}
            else:
                result = search_budget(part.relaxed, original_budget, 50000)
                assert result["status"] == "EXACT"
            components.append({"final": part.final,
                               "forbidden": sorted(part.relaxed.bad),
                               "active_proper_flags": sorted(part.active_flags),
                               "budget": result})
        values = [part["budget"]["budget"] for part in components
                  if part["budget"]["status"] == "EXACT"]
        assert values
        boundary_budget = min(values)
        output.append({"generator": row["generator"],
                       "flagged_budget": original_budget,
                       "full_boundary_budget": boundary_budget,
                       "proper_border_budget_increase": original_budget - boundary_budget,
                       "slices": components})
    return output


def main():
    counts = Counter()
    for instance in all_two_state_instances():
        counts["two_state_instances"] += 1
        check_instance(instance, 4, counts, is_small=True)
    for instance in generated_instances(20260905, 100):
        counts["random_instances"] += 1
        check_instance(instance, 7, counts)
    diagnostics = budget_diagnostics()
    result = {
        "status": "PASS",
        "two_state_max_word_length": 4,
        "random_seed": 20260905,
        "random_max_word_length": 7,
        "counts": dict(sorted(counts.items())),
        "prior_growth_diagnostics": diagnostics,
        "prior_growth_surviving_full_boundary_normalization": sum(
            row["proper_border_budget_increase"] > 0 for row in diagnostics),
        "scope": "exact boundary slices; certified regular subclass; at-most-two-state decision",
        "global_claim": "no decision procedure for unrestricted BorderAvoid or SEP",
    }
    (ROOT / "results/boundary-slices.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
