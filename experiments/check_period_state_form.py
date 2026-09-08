"""Finite checks for the shift/Z-array witness form and the single-source period form.

Written statements and proofs are in
notes/2026-09-08-strategy-review-and-period-state-form.md.  Everything here is
bounded regression evidence for the implementation and the stated lemmas; it is
not an all-length proof and it decides no unrestricted instance.  A search cap
is UNKNOWN, never NO.  Standard library only, Python 3.9+.
"""
import itertools
import json
import random
from collections import deque
from pathlib import Path

from border_lab import Instance, witness, words

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "results" / "period-state-form.json"


# ----------------------------------------------------------------------------
# Section 1: the shift / Z-array form of the witness predicate (any instance)
# ----------------------------------------------------------------------------

def z_array(rho):
    """Z(s) = length of the longest common prefix of rho and rho[s:], 1<=s<=|rho|."""
    n = len(rho)
    z = {}
    for s in range(1, n + 1):
        t = 0
        while s + t < n and rho[t] == rho[s + t]:
            t += 1
        z[s] = t
    return z


def shift_witness(I, w):
    """Witness iff admissible, diagonal-free, and every shift s satisfies
    not G(c'(s+t), c'(t)) for 0 <= t <= Z(s), with c'(x) = c(n-x)."""
    if not I.admissible(w):
        return False
    c = I.run(w)
    n = len(w)
    if any((q, q) in I.flags for q in c):
        return False
    rho = w[::-1]
    cp = c[::-1]
    z = z_array(rho)
    for s in range(1, n + 1):
        for t in range(z[s] + 1):
            if (cp[s + t], cp[t]) in I.flags:
                return False
    return True


def random_instance(k, rng, terminal=False):
    while True:
        delta = []
        for q in range(k):
            if terminal and q == k - 1:
                delta.append((-1, -1))
                continue
            delta.append(tuple(rng.randrange(k) if rng.random() < 0.8 else -1 for _ in range(2)))
        final = frozenset({k - 1}) if terminal else frozenset(rng.sample(range(k), rng.randrange(1, k + 1)))
        pairs = [(p, q) for p in range(k) for q in range(k)]
        flags = frozenset(rng.sample(pairs, rng.randrange(0, min(len(pairs), 6) + 1)))
        bad = frozenset(rng.sample(range(k), rng.randrange(0, 2))) if not terminal else frozenset()
        return Instance(tuple(delta), final, flags, bad)


def section_shift_form(rng, instances=300, max_len=7):
    compared = 0
    mismatches = []
    for case in range(instances):
        I = random_instance(rng.randrange(2, 6), rng, terminal=(case % 2 == 0))
        for w in words("01", max_len):
            compared += 1
            if witness(I, w) != shift_witness(I, w):
                mismatches.append({"delta": I.delta, "final": sorted(I.final),
                                   "flags": sorted(I.flags), "bad": sorted(I.bad), "word": w})
    return {"instances": instances, "max_word_length": max_len,
            "words_compared": compared, "mismatches": mismatches}


# ----------------------------------------------------------------------------
# Section 2: single-source instances and the period/state form
# ----------------------------------------------------------------------------

def valid_terminal(delta, k):
    reach = {0}
    stack = [0]
    while stack:
        q = stack.pop()
        for t in delta[q]:
            if t >= 0 and t not in reach:
                reach.add(t)
                stack.append(t)
    if k - 1 not in reach:
        return False
    coreach = {k - 1}
    changed = True
    while changed:
        changed = False
        for q in range(k):
            if q not in coreach and any(t in coreach for t in delta[q]):
                coreach.add(q)
                changed = True
    return reach & coreach == set(range(k))


def random_single_source(k, rng, max_targets=None):
    """Terminal DFA, start 0 with no incoming edge, final k-1 terminal, flags (0,q)."""
    while True:
        delta = []
        for q in range(k - 1):
            row = []
            for _ in range(2):
                if rng.random() < 0.8:
                    row.append(rng.randrange(1, k))  # never return to the start
                else:
                    row.append(-1)
            delta.append(tuple(row))
        delta.append((-1, -1))
        delta = tuple(delta)
        if not valid_terminal(delta, k):
            continue
        targets = list(range(1, k - 1))
        size = rng.randrange(1, len(targets) + 1) if max_targets is None else min(max_targets, len(targets))
        T = frozenset(rng.sample(targets, size))
        return Instance(delta, frozenset({k - 1}), frozenset((0, q) for q in T)), T


def periods(w):
    n = len(w)
    return [d for d in range(1, n) if all(w[i] == w[i + d] for i in range(n - d))]


def period_state_witness(I, T, w):
    """Single-source form: accepted, and no period d in [1,n) has c(d) in T."""
    if not I.admissible(w):
        return False
    c = I.run(w)
    return all(c[d] not in T for d in periods(w))


def shortest_witness(I, max_len):
    """BFS over defined runs by length.  Returns a word, 'NONE' (finite language
    exhausted), or None when the cap max_len is reached (UNKNOWN)."""
    level = [""]
    for _ in range(max_len + 1):
        for w in level:
            if I.admissible(w) and witness(I, w):
                return w
        nxt = []
        for w in level:
            q = I.run(w)[-1]
            for a, t in zip("01", I.delta[q]):
                if t >= 0:
                    nxt.append(w + a)
        level = nxt
        if not level:
            return "NONE"
    return None


def section_single_source(rng, instances=400, max_len=7, search_cap=14):
    compared = 0
    mismatches = []
    exponent_checks = 0
    exponent_failures = []
    periodic_shortest = 0
    unknown = 0
    none = 0
    for _ in range(instances):
        k = rng.randrange(3, 7)
        I, T = random_single_source(k, rng)
        for w in words("01", max_len):
            compared += 1
            if witness(I, w) != period_state_witness(I, T, w):
                mismatches.append({"delta": I.delta, "T": sorted(T), "word": w})
        # C038 at i=0 on a shortest witness: if the minimal period d0 <= n/2
        # then the exponent floor(n/d0) is at most k-1 and the states at the
        # multiples of d0 are pairwise distinct.
        w = shortest_witness(I, search_cap)
        if w is None:
            unknown += 1
        elif w == "NONE":
            none += 1
        elif w:
            per = periods(w)
            if per and per[0] <= len(w) // 2:
                periodic_shortest += 1
                d0 = per[0]
                c = I.run(w)
                e = len(w) // d0
                exponent_checks += 1
                states = [c[j * d0] for j in range(e + 1)]
                if e > k - 1 or len(set(states)) != len(states):
                    exponent_failures.append({"delta": I.delta, "T": sorted(T), "word": w})
    return {"instances": instances, "max_word_length": max_len, "search_cap": search_cap,
            "words_compared": compared, "mismatches": mismatches,
            "shortest_search_unknown": unknown, "finite_language_exhausted": none,
            "periodic_shortest_witnesses": periodic_shortest,
            "exponent_checks": exponent_checks, "exponent_failures": exponent_failures}


# ----------------------------------------------------------------------------
# Section 3: flag-count census (bounded data, lower bounds only)
# ----------------------------------------------------------------------------

def all_terminal_dfas(k):
    opts = list(range(-1, k))
    for rows in itertools.product(itertools.product(opts, repeat=2), repeat=k - 1):
        delta = tuple(rows) + ((-1, -1),)
        if valid_terminal(delta, k):
            yield delta


def census(k, nflags, max_len):
    hist = {}
    unknown = 0
    total = 0
    worst = None
    for delta in all_terminal_dfas(k):
        nonfinal = range(k - 1)
        pairs = [(p, q) for p in nonfinal for q in nonfinal if p != q]
        for G in itertools.combinations(pairs, nflags):
            I = Instance(delta, frozenset({k - 1}), frozenset(G))
            total += 1
            w = shortest_witness(I, max_len)
            if w is None:
                unknown += 1
                continue
            key = "none" if w == "NONE" else len(w)
            hist[str(key)] = hist.get(str(key), 0) + 1
            if w != "NONE" and (worst is None or len(w) > len(worst["word"])):
                worst = {"delta": delta, "flags": sorted(G), "word": w}
    return {"k": k, "flags": nflags, "instances": total, "search_cap": max_len,
            "shortest_length_histogram": dict(sorted(hist.items())),
            "unknown_at_cap": unknown, "longest_shortest_witness": worst}


def sampled_maxima(rng, k, nflags, trials, max_len):
    best = None
    unknown = 0
    for _ in range(trials):
        while True:
            delta = tuple(tuple(rng.randrange(k) if rng.random() < 0.8 else -1 for _ in range(2))
                          for _ in range(k - 1)) + ((-1, -1),)
            if valid_terminal(delta, k):
                break
        nonfinal = range(k - 1)
        pairs = [(p, q) for p in nonfinal for q in nonfinal if p != q]
        G = frozenset(rng.sample(pairs, nflags))
        I = Instance(delta, frozenset({k - 1}), G)
        w = shortest_witness(I, max_len)
        if w is None:
            unknown += 1
        elif w != "NONE" and (best is None or len(w) > len(best["word"])):
            best = {"delta": delta, "flags": sorted(G), "word": w}
    return {"k": k, "flags": nflags, "trials": trials, "search_cap": max_len,
            "unknown_at_cap": unknown, "longest_shortest_witness_found": best}


def main():
    rng = random.Random(2026090801)
    result = {"seed": 2026090801,
              "shift_form": section_shift_form(rng),
              "single_source": section_single_source(rng),
              "flag_census_k4": [census(4, 1, 12), census(4, 2, 12)],
              "flag_samples": [sampled_maxima(rng, k, f, 150, 14)
                               for k in (5, 6) for f in (1, 2, 3)]}
    checks = result["shift_form"]["mismatches"] == [] and \
        result["single_source"]["mismatches"] == [] and \
        result["single_source"]["exponent_failures"] == []
    result["status"] = "PASS" if checks else "FAIL"
    OUT.write_text(json.dumps(result, indent=1, sort_keys=True) + "\n")
    print(json.dumps({"status": result["status"],
                      "shift_words": result["shift_form"]["words_compared"],
                      "single_source_words": result["single_source"]["words_compared"],
                      "exponent_checks": result["single_source"]["exponent_checks"],
                      "census": [(c["k"], c["flags"], c["shortest_length_histogram"], c["unknown_at_cap"])
                                 for c in result["flag_census_k4"]],
                      "samples": [(s["k"], s["flags"], len(s["longest_shortest_witness_found"]["word"])
                                   if s["longest_shortest_witness_found"] else None)
                                  for s in result["flag_samples"]]}, indent=1))
    if not checks:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
