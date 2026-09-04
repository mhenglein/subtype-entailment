"""Reproduce the independent checks and counterexamples from this review."""

import json
import random
from pathlib import Path

from border_lab import (Instance, Sandwich, border_witness, first_end,
                        fixed_word_instance, lrs, memo_examples, necessary,
                        rigid, rigid_family, sufficient, suffix_trace_cut,
                        witness, word_budget, words)


def check():
    rng = random.Random(17082026)
    counts = {"words_checked": 0, "automaton_comparisons": 0,
              "sandwich_implications": 0, "truncations_checked": 0,
              "finite_state_searches": 0, "suffix_trace_cuts": 0,
              "profile_dominance_cuts": 0, "cuts_on_rigid_words": 0}
    search_statuses = {"YES": 0, "NO": 0, "UNKNOWN": 0}
    budgets = [(0, 0), (1, 0), (0, 1), (2, 0), (1, 1), (0, 2)]
    for case in range(80):
        k = rng.randrange(2, 6)
        density = (0, .04, .12, .25)[case % 4]
        I = Instance(
            tuple(tuple(-1 if rng.random() < .06 else rng.randrange(k) for _ in range(2)) for _ in range(k)),
            frozenset(q for q in range(k) if rng.random() < .4),
            frozenset((q, r) for q in range(k) for r in range(k) if rng.random() < density),
            frozenset(q for q in range(k) if rng.random() < .04),
        )
        machines = [(L, D, Sandwich(I, L, D), Sandwich(I, L, D, True)) for L, D in budgets]
        for w in words("01", 6):
            good = witness(I, w)
            assert good == border_witness(I, w), ("reversal", case, w)
            counts["words_checked"] += 1
            for L, D, nm, sm in machines:
                nv, sv = necessary(I, w, L, D), sufficient(I, w, L, D)
                assert nm.accepts(w) == nv, ("N automaton", case, w, L, D)
                assert sm.accepts(w) == sv, ("S automaton", case, w, L, D)
                assert not sv or good, ("sufficiency", case, w, L, D)
                assert not good or nv, ("necessity", case, w, L, D)
                counts["automaton_comparisons"] += 2
                counts["sandwich_implications"] += 2
            if good:
                assert sufficient(I, w, lrs(w), 0)
                if not w:
                    continue  # 8.15 needs nonempty pi for the strict e<n claim.
                c, n = I.run(w), len(w)
                for e in range(n):
                    for profiles, field in ((False, "suffix_trace_cuts"), (True, "profile_dominance_cuts")):
                        if suffix_trace_cut(I, w, e, use_profiles=profiles):
                            assert witness(I, w[:e]), ("new cut", case, w, e, profiles)
                            counts[field] += 1
                            if not profiles and rigid(I, w):
                                counts["cuts_on_rigid_words"] += 1
                for ell in range(lrs(w)+1):
                    e = first_end(w, ell)
                    if c[e-ell] == c[n-ell]:
                        short = w[:e]
                        assert e < n and witness(I, short), ("truncation", case, w, ell)
                        assert ell == 0 or lrs(short) < ell
                        counts["truncations_checked"] += 1
        for L, D, nm, sm in machines[:3]:
            for machine in (nm, sm):
                result = machine.search(max_states=30000)
                counts["finite_state_searches"] += 1
                search_statuses[result["status"]] += 1
                if result["status"] == "YES":
                    assert machine.accepts(result["word"])
                    if machine.strong:
                        assert witness(I, result["word"])

    I = rigid_family()
    rigid_rows = []
    for n in (1, 2, 3, 10, 100, 500):
        w = "0"*n
        assert witness(I, w) and rigid(I, w) and lrs(w) == n-1
        if n > 1:
            assert suffix_trace_cut(I, w, 1)
        rigid_rows.append({"length": n, "states": 2, "lrs": lrs(w),
                           "rigid": True, "word_budget": word_budget(I, w)})
    shortest = Sandwich(I, 0, 0, True).search()
    assert shortest["word"] == "0"

    singleton_rows = []
    for n in (1, 2, 3, 5, 8, 12):
        I, w = fixed_word_instance(n), "0"*n
        assert witness(I, w) and word_budget(I, w) == n-1
        results = []
        for budget in range(n):
            for L in range(budget+1):
                D = budget-L
                result = Sandwich(I, L, D, True).search()
                assert result["status"] == ("YES" if budget >= n-1 else "NO")
                results.append(result["states"])
        singleton_rows.append({"n": n, "states": n+1, "exact_instance_budget": n-1,
                               "emptiness_tests": len(results), "max_search_states": max(results)})

    example_rows = []
    for i, I in enumerate(memo_examples(), start=1):
        L, D = (0, 1) if i == 1 else (1, 0)
        answer = Sandwich(I, L, D).search()
        assert answer["status"] == "NO"
        example_rows.append({"example": "8.13("+str(i)+")", "L": L, "D": D, **answer})

    # Reproduce 3.2 directly from its closed-form push-only system.
    nonregular = []
    formula_disagreements = 0
    for w in words("01", 11):
        propagated = any(w == "0"*j+"1"+w[:p] for p in range(len(w)+1) for j in range(len(w)+1))
        first_one = w.find("1")
        periodic = False
        if first_one >= 0:
            block = w[:first_one+1]
            periodic = all(a == block[i % len(block)] for i, a in enumerate(w))
        assert propagated == periodic
        incorrect_formula = first_one >= 0
        formula_disagreements += incorrect_formula != propagated
        if propagated and w.count("1") == 2 and w.endswith("1"):
            nonregular.append(w)

    return {"seed": 17082026, "random_instances": 80, "max_word_length": 6,
            "checks": counts, "search_statuses": search_statuses, "failures": 0,
            "rigid_family": rigid_rows, "rigid_family_shortest": shortest,
            "singleton_budget_family": singleton_rows, "memo_no_examples": example_rows,
            "theorem_3_2": {"words_checked": 4095, "formula_disagreements": formula_disagreements,
                            "two_ones_language": nonregular}}


if __name__ == "__main__":
    result = check()
    out = Path(__file__).resolve().parents[1] / "results"
    out.mkdir(exist_ok=True)
    (out / "independent-checks.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))
