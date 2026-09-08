"""Exhaustive census of single-source terminal BorderAvoid instances.

An instance has k states: start 0 with no incoming transition, terminal final
k-1, every other state nonfinal, and flags (0,q) for q in a nonempty target set
T subset of {1,...,k-2}.  Tables are enumerated up to relabelling of the middle
states.  For each instance a shortest witness is found by breadth-first search
over defined runs; when the cap is reached the instance is certified NO only by
an exhausted Necessary(L,D) automaton (border_lab.Sandwich) at some small
budget, otherwise it is reported UNKNOWN.  A finite accepted language with no
witness is reported as 'none'.

Usage: python3 experiments/single_source_census.py K [CAP]

Writes results/single-source-census.json (merging the entry for K).  The k=5
run takes roughly ten minutes in CPython.  Written statements are in
notes/2026-09-08-strategy-review-and-period-state-form.md.  Standard library.
"""
import itertools
import json
import sys
from pathlib import Path

from border_lab import Instance, Sandwich
from check_period_state_form import shortest_witness, valid_terminal

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "results" / "single-source-census.json"


def canonical(delta, k):
    mid = list(range(1, k - 1))
    best = None
    for perm in itertools.permutations(mid):
        m = {0: 0, k - 1: k - 1, -1: -1}
        m.update({mid[i]: perm[i] for i in range(len(mid))})
        rows = [None] * k
        for q in range(k):
            rows[m[q]] = tuple(m[t] for t in delta[q])
        t = tuple(rows)
        if best is None or t < best:
            best = t
    return best


def census(k, cap, budget=4, max_states=50000):
    mid = list(range(1, k - 1))
    opts = [-1] + list(range(1, k))
    seen = set()
    hist = {}
    unknown = []
    worst = []
    total = 0
    for rows in itertools.product(itertools.product(opts, repeat=2), repeat=k - 1):
        delta = tuple(rows) + ((-1, -1),)
        if not valid_terminal(delta, k):
            continue
        c = canonical(delta, k)
        if c in seen:
            continue
        seen.add(c)
        for r in range(1, len(mid) + 1):
            for T in itertools.combinations(mid, r):
                I = Instance(c, frozenset({k - 1}), frozenset((0, q) for q in T))
                total += 1
                w = shortest_witness(I, cap)
                if w is None:
                    cert = None
                    for L in range(budget):
                        for D in range(budget):
                            if Sandwich(I, L, D).search(max_states=max_states)["status"] == "NO":
                                cert = (L, D)
                                break
                        if cert:
                            break
                    if cert:
                        hist["NO"] = hist.get("NO", 0) + 1
                    else:
                        unknown.append({"delta": c, "T": list(T)})
                    continue
                key = "none" if w == "NONE" else str(len(w))
                hist[key] = hist.get(key, 0) + 1
                if w != "NONE":
                    if not worst or len(w) > len(worst[0]["word"]):
                        worst = [{"delta": c, "T": list(T), "word": w}]
                    elif len(w) == len(worst[0]["word"]) and len(worst) < 20:
                        worst.append({"delta": c, "T": list(T), "word": w})
    return {"k": k, "search_cap": cap, "necessary_budget_tried": budget,
            "canonical_tables": len(seen), "instances": total,
            "shortest_length_histogram": dict(sorted(hist.items())),
            "unknown": unknown, "longest_shortest_witnesses": worst}


def main():
    k = int(sys.argv[1])
    cap = int(sys.argv[2]) if len(sys.argv) > 2 else 20
    result = census(k, cap)
    data = json.loads(OUT.read_text()) if OUT.exists() else {}
    data[str(k)] = result
    OUT.write_text(json.dumps(data, indent=1, sort_keys=True) + "\n")
    summary = dict(result)
    summary["longest_shortest_witnesses"] = len(result["longest_shortest_witnesses"])
    summary["unknown"] = len(result["unknown"])
    print(json.dumps(summary))


if __name__ == "__main__":
    main()
