#!/usr/bin/env python3
"""Independent exact supplied-prefix oracle and C029 cycle-route regressions.

Finite samples do not establish the general C029 decision theorem. Exhaustive
one/two-state decisions use the existing proved small-state completeness bound.
"""
from __future__ import annotations
import argparse
from collections import Counter
from dataclasses import replace
import hashlib
from itertools import product
import json
from pathlib import Path
import random

from border_lab import Instance, words, witness, border_witness
from safe_extensions import absorption_holds, safe_states, zero_region
from infinite_extensions import infinite_extension_decision
from infinite_cycle_monitor import (monitor_word, periodic_prefix_search,
                                    infinite_cycle_decision, safe_cycle)
from check_infinite_extensions import random_absorbing
from check_absorbing_terminal import decoded, absorbing, infinite_endpoints, has_witness

ROOT = Path(__file__).resolve().parents[1]


def suffix_oracle(I, prefix, period):
    """Direct infinite-word equality; no ray, phase buckets or primitive root.

    After n comparison positions both suffixes are in the d-periodic tail.
    Checking n+d positions therefore checks the ENTIRE infinite suffix pair.
    This is an all-length oracle for each supplied prefix, not an existence bound.
    """
    states = I.run(prefix)
    if states is None or any(q in I.bad or (q, q) in I.flags for q in states):
        return False
    n, d = len(prefix), len(period)
    def symbol(t):
        return prefix[t] if t < n else period[(t-n) % d]
    for i in range(n+1):
        for j in range(i+1, n+1):
            if (states[i], states[j]) in I.flags and all(
                    symbol(i+t) == symbol(j+t) for t in range(n+d)):
                return False
    return True


def plain(I):
    return Instance(I.delta, I.finals, I.flags, I.bad, I.initial)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT/"results/infinite-cycle-monitor.json")
    args = parser.parse_args()
    seed = 2026091929
    rng = random.Random(seed)
    counts = Counter()
    periods = list(words("01", 4))[1:]
    # Include every nonprimitive binary period through length four.
    for case in range(300):
        k = rng.randrange(2, 8)
        I = random_absorbing(rng, k)
        # Also arbitrary incoming columns to exercise the supplied-prefix monitor.
        if case % 2:
            I = replace(I, flags=frozenset((p,q) for p in range(k) for q in range(k)
                                         if rng.random() < .14))
        for prefix in words("01", 5):
            for period in periods:
                expected = suffix_oracle(I, prefix, period)
                actual = monitor_word(I, prefix, period)
                assert expected == actual, (I, prefix, period, expected, actual)
                counts["supplied_prefix_period_exact_oracle"] += 1
                run = I.run(prefix)
                if run is not None and all(q in safe_states(I) for q in run):
                    counts["safe_supplied_prefix_periods"] += 1
                    counts["safe_monitor_accept" if actual else "safe_monitor_reject"] += 1
    # Every partial transition/start/final/Bad/ordered-flag table for k<=2.
    for k in (1, 2):
        for data in product(range(k), range((k+1)**(2*k)), range(2**k),
                            range(2**k), range(2**(k*k))):
            A = decoded(k, *data)
            if not absorbing(A):
                continue
            I = plain(A)
            good = infinite_endpoints(A)
            expected = has_witness(replace(A, finals=A.finals & good))
            answer = infinite_cycle_decision(I)
            assert (answer["status"] == "YES") == expected, (I, answer, expected)
            assert answer["status"] != "UNKNOWN"
            if expected:
                assert witness(I, answer["word"]) and border_witness(I, answer["word"])
                assert I.run(answer["word"])[-1] in good
            counts["exhaustive_absorbing_"+str(k)+"_state"] += 1
            counts["exhaustive_"+answer["status"]] += 1
    examples = []
    for case in range(600):
        I = random_absorbing(rng, rng.randrange(2, 8))
        old = infinite_extension_decision(I, 100000)
        new = infinite_cycle_decision(I, 100000)
        assert old["status"] == new["status"], (I, old, new)
        counts["old_new_decision_agreement"] += 1
        counts["random_"+new["status"]] += 1
        if new["status"] == "YES":
            assert suffix_oracle(I, new["prefix"], new["cycle"])
            assert safe_cycle(I, new["target"], new["cycle"])
            assert I.run(new["word"])[-1] == new["target"]
            if len(examples) < 3:
                examples.append(new)
    # Nonprimitive equal rotations must count as equal suffixes.
    rotation = Instance(((1,-1),(2,-1),(2,-1)), frozenset({2}), frozenset({(0,1)}))
    assert not monitor_word(rotation, "00", "00")
    assert not suffix_oracle(rotation, "00", "00")
    # Ordered flags cannot be reversed.
    direction = replace(rotation, flags=frozenset({(1,0)}))
    assert monitor_word(direction, "00", "00")
    # A mismatch to the LEFT cannot repair an already-equal pair to its right.
    freeze = Instance(((-1,1),(2,-1),(3,-1),(3,-1)), frozenset({3}), frozenset({(1,2)}))
    assert not monitor_word(freeze, "100", "0")
    # A mismatching tail does eliminate a prior purely periodic comparison.
    nonpure = Instance(((1,-1),(2,-1),(3,-1),(-1,3)), frozenset({2,3}), frozenset({(0,1)}))
    assert infinite_cycle_decision(nonpure)["status"] == "YES"
    # The cap cannot be turned into a negative certificate.
    capped = infinite_cycle_decision(nonpure, max_states=1)
    assert capped["status"] == "UNKNOWN", capped
    # A genuine terminal witness remains outside the C029 target.
    terminal = Instance(((1,-1),(-1,-1)), frozenset({1}))
    assert witness(terminal, "0")
    assert infinite_cycle_decision(terminal)["status"] == "NO_INFINITE_EXTENSION"
    # Missing strong absorption is not silently accepted.
    invalid = Instance(((1,-1),(-1,-1)), frozenset({0}))
    assert infinite_cycle_decision(invalid)["status"] == "UNKNOWN"
    # A longer pre-final loop is necessary; shortest safe entry fails.
    loop = Instance(((1,-1),(2,1),(2,-1)), frozenset({2}), frozenset({(0,1)}))
    assert not monitor_word(loop, "00", "0")
    assert monitor_word(loop, "010", "0")
    assert witness(loop, "0100") and not witness(loop, "010")
    loop_answer = infinite_cycle_decision(loop)
    assert loop_answer["status"] == "YES" and len(loop_answer["prefix"]) > 2
    # A branch exit can yield only a terminal witness, despite a reachable cycle.
    terminal_exit = Instance(((1,-1),(2,-1),(2,3),(-1,-1)),
                             frozenset({2,3}), frozenset({(0,1)}))
    assert witness(terminal_exit, "001")
    assert infinite_cycle_decision(terminal_exit)["status"] == "NO_INFINITE_EXTENSION"
    counts["targeted_guards"] = 9
    sources = ["experiments/infinite_cycle_monitor.py", "experiments/check_infinite_cycle_monitor.py"]
    result = dict(status="PASS", seed=seed, counts=dict(counts), examples=examples, prefinal_loop_example=loop_answer,
                  source_sha256={p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sources},
                  scope="Exact per-prefix infinite-suffix oracle; complete one/two-state decisions; finite larger-state differential evidence. General monitor and C029 correctness not yet Lean-checked.")
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True)+"\n")
    print(json.dumps({"status":result["status"],"counts":counts,"output":str(args.output)}, sort_keys=True))


if __name__ == "__main__":
    main()
