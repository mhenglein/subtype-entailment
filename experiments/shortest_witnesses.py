"""Exhaustive shortest-witness search for two-state BorderAvoid instances.

The search covers every binary two-state partial instance with start state 0,
including all ``Bad``, ``Fin``, and flag relations.  It scans words by
increasing length.  A shortestness result is certified only after every
earlier word length has been checked.  The word cap is a scan limit, not a
claim that longer words do not exist.

The finite ``Sandwich`` calls are separate diagnostics.  ``NO_THROUGH`` means
that a requested budget range was exhausted, while ``UNKNOWN`` means a state
cap interrupted the graph search.  Neither status is a global NO result.

Run from the repository root:

    python3 experiments/shortest_witnesses.py
"""

from __future__ import annotations

import argparse
import itertools
import json
import random
import sys
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Sequence, Tuple


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from experiments.border_lab import (  # noqa: E402
    Instance,
    Sandwich,
    border_witness,
    necessary,
    sufficient,
)


def all_two_state_instances() -> Iterable[Instance]:
    """Enumerate exactly 3^4 * 4 * 4 * 16 = 20,736 instances."""

    values = range(-1, 2)
    subsets = [
        frozenset(q for q in range(2) if mask >> q & 1)
        for mask in range(4)
    ]
    flags = [
        frozenset(
            (q, r)
            for q in range(2)
            for r in range(2)
            if mask >> (2 * q + r) & 1
        )
        for mask in range(16)
    ]
    for flat in itertools.product(values, repeat=4):
        delta = (flat[:2], flat[2:])
        for final in subsets:
            for bad in subsets:
                for relation in flags:
                    yield Instance(delta, final, relation, bad)


def words_by_length(alphabet: str, max_length: int) -> Iterable[str]:
    for length in range(max_length + 1):
        for letters in itertools.product(alphabet, repeat=length):
            yield "".join(letters)


def run(instance: Instance, word: str) -> Optional[Tuple[int, ...]]:
    """Independent DFA run used as the primary witness oracle."""

    states = [instance.start]
    for letter in word:
        target = instance.delta[states[-1]][instance.alphabet.index(letter)]
        if target < 0:
            return None
        states.append(target)
    return tuple(states)


def direct_witness(instance: Instance, word: str) -> bool:
    """Independent forward form of Definition 8.1."""

    states = run(instance, word)
    if states is None or states[-1] not in instance.final:
        return False
    if any(state in instance.bad for state in states):
        return False
    n = len(word)
    return not any(
        word[i:].startswith(word[j:]) and (states[i], states[j]) in instance.flags
        for i in range(n + 1)
        for j in range(i, n + 1)
    )


def longest_repeated_suffix(word: str) -> int:
    for length in range(len(word) - 1, 0, -1):
        if word[-length:] in word[:-1]:
            return length
    return 0


def first_end(word: str, length: int) -> int:
    if length == 0:
        return 0
    return word.index(word[-length:]) + length


def independent_word_budget(instance: Instance, word: str) -> Optional[int]:
    """Compute the per-word L+D budget independently of border_lab."""

    if not direct_witness(instance, word):
        return None
    n = len(word)
    return min(
        L + (n - first_end(word, L + 1) if L < n else 0)
        for L in range(n + 1)
    )


def sufficient_at_minimum_word_budget(instance: Instance, word: str) -> bool:
    """Check the strong predicate at at least one minimizing split."""

    budget = independent_word_budget(instance, word)
    if budget is None:
        return False
    n = len(word)
    for L in range(n + 1):
        value = L + (n - first_end(word, L + 1) if L < n else 0)
        if value == budget and sufficient(instance, word, L, budget - L):
            return True
    return False


def encode_instance(instance: Instance) -> Dict[str, object]:
    return {
        "alphabet": instance.alphabet,
        "start": instance.start,
        "delta": [list(row) for row in instance.delta],
        "final": sorted(instance.final),
        "bad": sorted(instance.bad),
        "flags": [list(pair) for pair in sorted(instance.flags)],
    }


def classify_word(instance: Instance, word: str) -> Tuple[str, Dict[str, object]]:
    """Explain why a checked non-witness failed."""

    states = run(instance, word)
    if states is None:
        return "undefined_transition", {}
    bad_states = sorted(set(states).intersection(instance.bad))
    if bad_states:
        return "bad_state", {"states": bad_states}
    if states[-1] not in instance.final:
        return "non_final", {"end_state": states[-1]}
    blockers = [
        {
            "i": i,
            "j": j,
            "pair": [states[i], states[j]],
            "suffix_at_i": word[i:],
            "suffix_at_j": word[j:],
        }
        for i in range(len(word) + 1)
        for j in range(i, len(word) + 1)
        if word[i:].startswith(word[j:])
        and (states[i], states[j]) in instance.flags
    ]
    if blockers:
        return "flagged_border", {"blocking_pairs": blockers[:4]}
    return "oracle_mismatch", {}


def context_cut(
    instance: Instance, word: str, end: int, mode: str
) -> bool:
    """Check C008, C009, or the proved visited-state refinement."""

    states = run(instance, word)
    if states is None or not direct_witness(instance, word):
        return False
    short = word[:end]
    h = longest_repeated_suffix(short)
    if h and short[-h:] != word[-h:]:
        return False
    if states[end] not in instance.final:
        return False
    if mode == "equal":
        return states[end - h] == states[len(word) - h]

    if mode == "profile":
        sources = set(range(len(instance.delta)))
    elif mode == "visited":
        sources = set(states[: end + 1])
    else:
        raise ValueError(mode)
    for length in range(h + 1):
        new_target = states[end - length]
        old_target = states[len(word) - length]
        for source in sources:
            if (source, new_target) in instance.flags and (
                source,
                old_target,
            ) not in instance.flags:
                return False
    return True


def failure_summary(
    instance: Instance, checked_words: Sequence[str], shortest: Optional[str]
) -> Dict[str, object]:
    counts = {
        "undefined_transition": 0,
        "bad_state": 0,
        "non_final": 0,
        "flagged_border": 0,
        "oracle_mismatch": 0,
    }
    examples: Dict[str, Dict[str, object]] = {}
    for word in checked_words:
        if shortest is not None and len(word) >= len(shortest):
            continue
        if direct_witness(instance, word):
            continue
        category, detail = classify_word(instance, word)
        counts[category] += 1
        examples.setdefault(category, {"word": word, **detail})
    return {"counts": counts, "examples": examples}


def shortest_row(
    instance: Instance,
    word: str,
    checked_words: Sequence[str],
    cut_counts: Dict[str, int],
    cut_failures: List[Dict[str, object]],
) -> Dict[str, object]:
    states = run(instance, word)
    if states is None:
        raise AssertionError("shortest witness has undefined run")
    budget = independent_word_budget(instance, word)
    if budget is None:
        raise AssertionError("shortest word failed independent budget")
    if not sufficient_at_minimum_word_budget(instance, word):
        raise AssertionError("shortest word failed sufficient predicate")
    return {
        "instance": encode_instance(instance),
        "shortest_word": word,
        "shortest_length": len(word),
        "state_trace": list(states),
        "lrs": longest_repeated_suffix(word),
        "per_word_budget": budget,
        "checked_words": len(checked_words),
        "shortestness_certified": True,
        "shorter_failure_summary": failure_summary(instance, checked_words, word),
        "cut_diagnostics": {
            "c008_equal_state_applicable": cut_counts["equal"],
            "c009_all_state_profile_applicable": cut_counts["profile"],
            "c013_visited_state_profile_applicable": cut_counts["visited"],
            "unexpected_cut_failures": cut_failures,
        },
    }


def search_budget(
    instance: Instance, max_budget: int, state_cap: int, strong: bool
) -> Dict[str, object]:
    """Search increasing fixed budgets with exact cap/status semantics."""

    splits_checked = 0
    lower_no_splits = 0
    for budget in range(max_budget + 1):
        for L in range(budget + 1):
            D = budget - L
            splits_checked += 1
            result = Sandwich(instance, L, D, strong=strong).search(
                max_states=state_cap
            )
            if result["status"] == "YES":
                word = result["word"]
                if strong and not direct_witness(instance, word):
                    raise AssertionError("Sandwich returned a non-witness")
                if strong and not border_witness(instance, word):
                    raise AssertionError("reverse oracle rejected Sandwich word")
                sufficient_ok = sufficient(instance, word, L, D)
                if strong and not sufficient_ok:
                    raise AssertionError("strong Sandwich word failed sufficient predicate")
                if not strong and not necessary(instance, word, L, D):
                    raise AssertionError("necessary search word failed its predicate")
                return {
                    "status": "EXACT",
                    "budget": budget,
                    "split": {"L": L, "D": D},
                    "word": word,
                    "word_length": len(word),
                    "sufficient_predicate": sufficient_ok,
                    "search_states": result["states"],
                    "splits_checked": splits_checked,
                    "lower_no_splits": lower_no_splits,
                }
            if result["status"] == "UNKNOWN":
                return {
                    "status": "UNKNOWN",
                    "first_unknown": {
                        "budget": budget,
                        "split": {"L": L, "D": D},
                        "states": result["states"],
                        "reason": result.get("reason", "unspecified"),
                    },
                    "splits_checked": splits_checked,
                    "lower_no_splits": lower_no_splits,
                }
            if result["status"] != "NO":
                raise AssertionError(f"unexpected Sandwich status {result['status']}")
            lower_no_splits += 1
    return {
        "status": "NO_THROUGH",
        "through_budget": max_budget,
        "splits_checked": splits_checked,
        "lower_no_splits": lower_no_splits,
    }


def boundary_slice(instance: Instance, final_state: int) -> Instance:
    """Drop all flags after conservative full-boundary normalization."""

    diagonal_bad = {
        q for q in range(len(instance.delta)) if (q, q) in instance.flags
    }
    full_boundary_bad = {
        q for q in range(len(instance.delta)) if (q, final_state) in instance.flags
    }
    return Instance(
        instance.delta,
        frozenset({final_state}),
        frozenset(),
        instance.bad | diagonal_bad | full_boundary_bad,
        instance.start,
        instance.alphabet,
    )


def boundary_diagnostic(
    instance: Instance,
    original_budget: int,
    state_cap: int,
    word_cap: Optional[int] = None,
) -> Dict[str, object]:
    """Compare the original word budget with exact final-state slices."""

    slices = []
    max_budget = max(8, original_budget)
    for final_state in sorted(instance.final):
        sliced = boundary_slice(instance, final_state)
        empty_reason = global_no_reason(sliced)
        if empty_reason is not None:
            result = {
                "status": "EXACT_NO",
                "reason": empty_reason,
                "search_skipped": True,
            }
        else:
            result = search_budget(sliced, max_budget, state_cap, strong=True)
        row = {
            "final_state": final_state,
            "slice_instance": encode_instance(sliced),
            "diagonal_states_added": sorted(
                q for q in range(len(instance.delta)) if (q, q) in instance.flags
            ),
            "full_boundary_states_added": sorted(
                q
                for q in range(len(instance.delta))
                if (q, final_state) in instance.flags
            ),
            "search": result,
        }
        if word_cap is not None:
            if empty_reason is not None:
                row["shortest_to_word_cap"] = {
                    "status": "EXACT_NO",
                    "reason": empty_reason,
                    "search_skipped": True,
                }
            else:
                row["shortest_to_word_cap"] = bounded_shortest_summary(
                    sliced, word_cap
                )
        slices.append(row)
    exact = [
        int(row["search"]["budget"])
        for row in slices
        if row["search"].get("status") == "EXACT"
    ]
    upper = min(exact) if exact else None
    # An unresolved slice must not hide a lower budget than the best known
    # slice. UNKNOWN at budget b still certifies all budgets below b empty.
    def excludes_below(result, budget):
        if result["status"] == "EXACT_NO":
            return True
        if result["status"] == "EXACT":
            return int(result["budget"]) >= budget
        if result["status"] == "NO_THROUGH":
            return int(result["through_budget"]) >= budget - 1
        return int(result["first_unknown"]["budget"]) >= budget

    certified = upper is not None and all(
        excludes_below(row["search"], upper) for row in slices
    )
    minimum = upper if certified else None
    return {
        "slices": slices,
        "boundary_budget_status": "EXACT" if certified else "UNKNOWN",
        "boundary_budget_upper_bound": upper,
        "minimum_exact_slice_budget": minimum,
        "original_per_word_budget": original_budget,
        "selected_word_budget_growth_vs_slice": None
        if minimum is None
        else original_budget - minimum,
    }


def add_boundary_diagnostics(
    rows: List[Dict[str, object]], state_cap: int
) -> None:
    for row in rows:
        instance = decode_instance(row["instance"])
        row["boundary_normalization"] = boundary_diagnostic(
            instance, int(row["per_word_budget"]), state_cap
        )


def global_no_reason(instance: Instance) -> Optional[str]:
    """Return a finite reachability reason for an empty admissible language."""

    if not instance.final:
        return "empty_final_set"
    if instance.start in instance.bad:
        return "bad_initial_state"
    reachable = {instance.start}
    frontier = [instance.start]
    while frontier:
        state = frontier.pop()
        for target in instance.delta[state]:
            if target >= 0 and target not in instance.bad and target not in reachable:
                reachable.add(target)
                frontier.append(target)
    if not reachable.intersection(instance.final):
        return "no_reachable_non_bad_final_state"
    return None


def select_no_witness_instances(
    instances: Sequence[Instance], limit: int
) -> List[Instance]:
    """Choose diverse no-witness rows for exact fixed-N diagnostics."""

    selected: List[Instance] = []
    seen_reasons = set()
    for instance in instances:
        reason = global_no_reason(instance)
        if reason is not None and reason not in seen_reasons:
            selected.append(instance)
            seen_reasons.add(reason)
            if len(selected) >= limit:
                return selected
    for instance in instances:
        if instance not in selected:
            selected.append(instance)
            if len(selected) >= limit:
                break
    return selected


def decode_instance(data: Dict[str, object]) -> Instance:
    return Instance(
        tuple(tuple(row) for row in data["delta"]),
        frozenset(data["final"]),
        frozenset(tuple(pair) for pair in data["flags"]),
        frozenset(data["bad"]),
        int(data["start"]),
        str(data["alphabet"]),
    )


def pairset(instance: Instance, word: str) -> frozenset[Tuple[int, int]]:
    """State pairs that would reject ``word`` if flagged."""

    states = run(instance, word)
    if states is None:
        return frozenset()
    return frozenset(
        (states[i], states[j])
        for i in range(len(word) + 1)
        for j in range(i, len(word) + 1)
        if word[i:].startswith(word[j:])
    )


def admissible(instance: Instance, word: str) -> bool:
    states = run(instance, word)
    return (
        states is not None
        and states[-1] in instance.final
        and not set(states).intersection(instance.bad)
    )


def random_target_base(rng, states: int) -> Instance:
    """Generate a base language for witness-preserving flag mutations."""

    p_undefined = rng.choice((0.01, 0.04, 0.08, 0.14))
    delta = tuple(
        tuple(
            -1 if rng.random() < p_undefined else rng.randrange(states)
            for _ in range(2)
        )
        for _ in range(states)
    )
    final = frozenset(q for q in range(1, states) if rng.random() < 0.35)
    if not final:
        final = frozenset({rng.randrange(1, states)})
    bad = frozenset(q for q in range(states) if rng.random() < 0.02)
    return Instance(delta, final, frozenset(), bad)


def targeted_attempt(
    rng, attempt: int, max_word_length: int, steps: int
) -> Optional[Dict[str, object]]:
    """Raise shortest length by adding flags while preserving a long target."""

    states = rng.randint(3, 8)
    base = random_target_base(rng, states)
    candidates = [
        (word, pairset(base, word))
        for word in words_by_length(base.alphabet, max_word_length)
        if admissible(base, word)
    ]
    if not candidates:
        return None
    candidate_scores = {
        word: (
            independent_word_budget(base, word),
            longest_repeated_suffix(word),
        )
        for word, _ in candidates
    }

    flags = set()
    best: Optional[Tuple[Tuple[int, int, int], Instance, str, int]] = None
    steps_done = 0
    for step in range(steps + 1):
        available = [
            (word, pairs)
            for word, pairs in candidates
            if not flags.intersection(pairs)
        ]
        if not available:
            break
        current_word, current_pairs = available[0]
        current = Instance(
            base.delta,
            base.final,
            frozenset(flags),
            base.bad,
            base.start,
            base.alphabet,
        )
        if not direct_witness(current, current_word):
            raise AssertionError("targeted available word is not a witness")
        if not border_witness(current, current_word):
            raise AssertionError("targeted word failed reverse oracle")
        budget = independent_word_budget(current, current_word)
        if budget is None:
            raise AssertionError("targeted witness has no word budget")
        score = (len(current_word), budget, longest_repeated_suffix(current_word))
        if best is None or score > best[0]:
            best = (score, current, current_word, step)
        if step == steps:
            break

        # Preserve a longer admissible word.  Prefer long words with small
        # pairsets, since they leave more choices for future flags.
        targets = [
            (word, pairs)
            for word, pairs in available[1:]
            if len(word) > len(current_word)
        ]
        targets.sort(
            key=lambda item: (
                -int(candidate_scores[item[0]][0]),
                -int(candidate_scores[item[0]][1]),
                -len(item[0]),
                len(item[1]),
                item[0],
            )
        )
        choice = None
        for target_word, target_pairs in targets:
            difference = sorted(current_pairs - target_pairs)
            if difference:
                choice = difference[0]
                break
        if choice is None:
            break
        flags.add(choice)
        steps_done = step + 1

    if best is None:
        return None
    score, instance, current_word, best_step = best
    return {
        "attempt": attempt,
        "steps_requested": steps,
        "steps_done": steps_done,
        "best_step": best_step,
        "base_instance": encode_instance(base),
        "instance": encode_instance(instance),
        "shortest_word": current_word,
        "shortest_length": score[0],
        "per_word_budget": score[1],
        "lrs": score[2],
        "base_flags": [],
        "targeted_flags": [list(pair) for pair in sorted(instance.flags)],
        "admissible_base_words_to_cap": len(candidates),
    }


def bounded_shortest_summary(
    instance: Instance, max_word_length: int
) -> Dict[str, object]:
    """Find the first witness through a finite word cap."""

    checked = 0
    for word in words_by_length(instance.alphabet, max_word_length):
        checked += 1
        ours = direct_witness(instance, word)
        reference = border_witness(instance, word)
        if ours != reference:
            raise AssertionError("summary forward/reverse oracle disagreement")
        if ours:
            budget = independent_word_budget(instance, word)
            if budget is None:
                raise AssertionError("summary witness has no word budget")
            if not sufficient_at_minimum_word_budget(instance, word):
                raise AssertionError("summary witness failed sufficient predicate")
            return {
                "status": "YES",
                "word": word,
                "length": len(word),
                "lrs": longest_repeated_suffix(word),
                "per_word_budget": budget,
                "words_checked": checked,
                "certified_through_length": len(word),
            }
    return {
        "status": "UNKNOWN",
        "word_cap": max_word_length,
        "words_checked": checked,
    }


def proper_border_pairs(instance: Instance, word: str) -> List[List[int]]:
    """Return flagged pairs used by nonempty, nonfull proper borders."""

    states = run(instance, word)
    if states is None:
        return []
    pairs = {
        (states[i], states[j])
        for i in range(len(word) + 1)
        for j in range(i + 1, len(word))
        if word[i:].startswith(word[j:])
    }
    return [list(pair) for pair in sorted(pairs.intersection(instance.flags))]


def boundary_flag_pairs(instance: Instance, word: str) -> List[List[int]]:
    """Return active empty/full-border flag pairs for ``word``."""

    states = run(instance, word)
    if states is None:
        return []
    n = len(word)
    pairs = {
        (states[i], states[j])
        for i in range(n + 1)
        for j in range(i, n + 1)
        if (i == j or j == n) and word[i:].startswith(word[j:])
    }
    return [list(pair) for pair in sorted(pairs.intersection(instance.flags))]


def proper_border_analysis(
    instance: Instance,
    word: str,
    base: Instance,
    max_word_length: int,
    budget_search_result: Dict[str, object],
    boundary_result: Dict[str, object],
) -> Dict[str, object]:
    """Compare a selected witness with the finite boundary-only baseline."""

    state_count = len(instance.delta)
    bound = max(0, state_count - 2)
    exact_budget = (
        int(budget_search_result["budget"])
        if budget_search_result.get("status") == "EXACT"
        else None
    )
    boundary_lengths = [
        int(row["shortest_to_word_cap"]["length"])
        for row in boundary_result.get("slices", [])
        if row.get("shortest_to_word_cap", {}).get("status") == "YES"
    ]
    normalized_budgets = [
        int(row["search"]["budget"])
        for row in boundary_result.get("slices", [])
        if row.get("search", {}).get("status") == "EXACT"
    ]
    proper_pairs_before_word = set()
    proper_examples = []
    for candidate in words_by_length(base.alphabet, max_word_length):
        if len(candidate) >= len(word) or not admissible(base, candidate):
            continue
        if direct_witness(instance, candidate):
            continue
        pairs = proper_border_pairs(instance, candidate)
        if not pairs:
            continue
        proper_pairs_before_word.update(tuple(pair) for pair in pairs)
        if len(proper_examples) < 8:
            boundary_pairs = boundary_flag_pairs(instance, candidate)
            proper_examples.append(
                {
                    "word": candidate,
                    "flag_pairs": pairs,
                    "boundary_flag_pairs": boundary_pairs,
                    "boundary_safe": not boundary_pairs,
                }
            )
    return {
        "state_count": state_count,
        "boundary_budget_bound": bound,
        "exact_instance_budget": exact_budget,
        "budget_excess_over_boundary_bound": (
            None if exact_budget is None else exact_budget - bound
        ),
        "minimum_normalized_slice_budget": (
            min(normalized_budgets) if normalized_budgets else None
        ),
        "exact_budget_growth_vs_normalized_slice": (
            None
            if exact_budget is None or not normalized_budgets
            else exact_budget - min(normalized_budgets)
        ),
        "selected_word_length": len(word),
        "minimum_normalized_slice_length": (
            min(boundary_lengths) if boundary_lengths else None
        ),
        "selected_length_minus_normalized_slice": (
            None
            if not boundary_lengths
            else len(word) - min(boundary_lengths)
        ),
        "proper_flag_pairs_on_selected_word": proper_border_pairs(instance, word),
        "proper_flag_pairs_blocking_shorter_base_words": [
            list(pair) for pair in sorted(proper_pairs_before_word)
        ],
        "properly_blocked_shorter_example_count": len(proper_examples),
        "boundary_safe_proper_example_count": sum(
            bool(example["boundary_safe"]) for example in proper_examples
        ),
        "proper_blocked_shorter_examples": proper_examples,
    }


def complete_targeted_row(
    row: Dict[str, object],
    max_word_length: int,
    state_cap: int,
) -> Dict[str, object]:
    """Independently certify the targeted row through the word cap."""

    instance = decode_instance(row["instance"])
    checked: List[str] = []
    found = None
    for word in words_by_length(instance.alphabet, max_word_length):
        checked.append(word)
        ours = direct_witness(instance, word)
        reference = border_witness(instance, word)
        if ours != reference:
            raise AssertionError("targeted forward/reverse oracle disagreement")
        if ours:
            found = word
            break
    if found is None:
        raise AssertionError("targeted mutation lost its preserved witness")
    if found != row["shortest_word"]:
        raise AssertionError("targeted shortest word changed during replay")
    trace = run(instance, found)
    if trace is None:
        raise AssertionError("targeted witness has no state trace")
    row["state_trace"] = list(trace)
    row["visited_states"] = sorted(set(trace))
    row["shortestness"] = {
        "certified_through_length": len(found),
        "words_checked": len(checked),
        "forward_reverse_comparisons": len(checked),
        "failure_summary": failure_summary(instance, checked, found),
    }
    row["cuts"] = {
        mode: sum(
            context_cut(instance, found, end, mode)
            for end in range(len(found))
        )
        for mode in ("equal", "profile", "visited")
    }
    row["budget_search"] = search_budget(
        instance,
        max(8, int(row["per_word_budget"])),
        state_cap,
        strong=True,
    )
    base = decode_instance(row["base_instance"])
    row["base_shortest"] = {
        "summary": bounded_shortest_summary(base, max_word_length),
        "budget_search": search_budget(base, 8, state_cap, strong=True),
    }
    boundary_result = boundary_diagnostic(
        instance,
        int(row["per_word_budget"]),
        state_cap,
        word_cap=max_word_length,
    )
    row["boundary_normalization"] = boundary_result
    row["proper_border_analysis"] = proper_border_analysis(
        instance,
        found,
        base,
        max_word_length,
        row["budget_search"],
        boundary_result,
    )
    return row


def run_search(args: argparse.Namespace) -> Dict[str, object]:
    words = list(words_by_length("01", args.max_word_length))
    two_state_scan_length = min(args.max_word_length, 1)
    scan_words = list(words_by_length("01", two_state_scan_length))
    total_instances = 0
    total_words_checked = 0
    oracle_comparisons = 0
    failures: List[Dict[str, object]] = []
    shortest_rows: List[Dict[str, object]] = []
    no_witness_instances: List[Instance] = []
    cut_applicable = {"equal": 0, "profile": 0, "visited": 0}
    cut_failures: List[Dict[str, object]] = []
    length_histogram: Dict[str, int] = {}
    lrs_histogram: Dict[str, int] = {}
    budget_histogram: Dict[str, int] = {}
    failure_categories = {
        "undefined_transition": 0,
        "bad_state": 0,
        "non_final": 0,
        "flagged_border": 0,
        "oracle_mismatch": 0,
    }
    two_state_no_results: Dict[str, Dict[str, object]] = {}
    two_state_status_counts = {"NO": 0, "UNKNOWN": 0, "YES_FALLBACK": 0}
    two_state_state_histogram: Dict[str, int] = {}
    fallback_instances = 0

    for instance in all_two_state_instances():
        total_instances += 1
        checked: List[str] = []
        found: Optional[str] = None
        for word in scan_words:
            checked.append(word)
            total_words_checked += 1
            ours = direct_witness(instance, word)
            reference = border_witness(instance, word)
            oracle_comparisons += 1
            if ours != reference:
                failures.append(
                    {"kind": "witness_oracle", "word": word, "instance": encode_instance(instance)}
                )
                break
            if ours:
                found = word
                break
        if failures:
            break
        if found is None:
            # For two states, the exact N''(0,0) graph is a finite shortcut.
            # If it is empty, every witness is absent.  If a cap interrupts
            # it, retain UNKNOWN.  A nonempty result falls back to the full
            # requested word cap so the census remains sound.
            if args.max_word_length >= 1:
                necessary_n00 = Sandwich(instance, 0, 0, strong=False).search(
                    max_states=args.state_cap
                )
                status_key = (
                    "YES_FALLBACK"
                    if necessary_n00["status"] == "YES"
                    else necessary_n00["status"]
                )
                two_state_status_counts[status_key] += 1
                state_count_key = str(necessary_n00.get("states", 0))
                two_state_state_histogram[state_count_key] = (
                    two_state_state_histogram.get(state_count_key, 0) + 1
                )
                key = json.dumps(encode_instance(instance), sort_keys=True)
                two_state_no_results[key] = necessary_n00
                if necessary_n00["status"] == "NO":
                    no_witness_instances.append(instance)
                    continue
                if necessary_n00["status"] == "UNKNOWN":
                    no_witness_instances.append(instance)
                    continue
                fallback_instances += 1
                for word in words[len(scan_words) :]:
                    checked.append(word)
                    total_words_checked += 1
                    ours = direct_witness(instance, word)
                    reference = border_witness(instance, word)
                    oracle_comparisons += 1
                    if ours != reference:
                        failures.append(
                            {
                                "kind": "witness_oracle",
                                "word": word,
                                "instance": encode_instance(instance),
                            }
                        )
                        break
                    if ours:
                        found = word
                        break
                if failures:
                    break
                if found is None:
                    no_witness_instances.append(instance)
                    continue
            else:
                no_witness_instances.append(instance)
                continue

        cut_counts = {"equal": 0, "profile": 0, "visited": 0}
        local_cut_failures: List[Dict[str, object]] = []
        for end in range(len(found)):
            for mode in cut_counts:
                if not context_cut(instance, found, end, mode):
                    continue
                cut_counts[mode] += 1
                cut_applicable[mode] += 1
                if not direct_witness(instance, found[:end]):
                    local_cut_failures.append(
                        {"mode": mode, "word": found, "end": end}
                    )
        cut_failures.extend(local_cut_failures)
        row = shortest_row(instance, found, checked, cut_counts, local_cut_failures)
        shortest_rows.append(row)
        for category, count in row["shorter_failure_summary"]["counts"].items():
            failure_categories[category] += int(count)
        length = str(row["shortest_length"])
        lrs = str(row["lrs"])
        budget = str(row["per_word_budget"])
        length_histogram[length] = length_histogram.get(length, 0) + 1
        lrs_histogram[lrs] = lrs_histogram.get(lrs, 0) + 1
        budget_histogram[budget] = budget_histogram.get(budget, 0) + 1

    # Keep only complete input descriptions for extremal rows.  The full
    # two-state census is represented by counts and histograms, not repeated
    # JSON rows.
    def top_by(key: str, limit: int = 5) -> List[Dict[str, object]]:
        return sorted(
            shortest_rows,
            key=lambda row: (
                int(row[key]),
                int(row["lrs"]),
                int(row["per_word_budget"]),
                -len(row["shortest_word"]),
                row["shortest_word"],
            ),
            reverse=True,
        )[:limit]

    extremals: List[Dict[str, object]] = []
    seen = set()
    for group in (top_by("shortest_length"), top_by("lrs"), top_by("per_word_budget")):
        for row in group:
            key = json.dumps(row["instance"], sort_keys=True)
            if key not in seen:
                seen.add(key)
                extremals.append(row)
    add_boundary_diagnostics(extremals, args.state_cap)

    # For no-witness cases, try a few exact necessary searches.  Empty final
    # sets and bad initial states have finite, explicit global NO reasons; the
    # other selected rows receive only a fixed N'' diagnostic.
    no_witness_diagnostics = []
    selected_no_witness = select_no_witness_instances(
        no_witness_instances, args.no_witness_checks
    )
    for instance in selected_no_witness:
        necessary = Sandwich(
            instance,
            args.max_word_length,
            0,
            strong=False,
        ).search(max_states=args.state_cap)
        if necessary["status"] == "YES":
            raise AssertionError("necessary N'' search returned a nonempty row")
        reason = global_no_reason(instance)
        no_witness_diagnostics.append(
            {
                "instance": encode_instance(instance),
                "necessary_search": {
                    "kind": "N''",
                    "L": args.max_word_length,
                    "D": 0,
                    "strong": False,
                    "result": necessary,
                    "graph_exhausted": necessary["status"] == "NO",
                },
                "two_state_n00_search": two_state_no_results.get(
                    json.dumps(encode_instance(instance), sort_keys=True)
                ),
                "global_no_certificate": reason,
            }
        )

    # The targeted stage mutates flags while preserving a long admissible base
    # word.  It is a bounded structural probe for 3--8 state examples, not a
    # random census and not a claim about all instances.
    rng = random.Random(args.targeted_seed)
    targeted_candidates = []
    for attempt in range(args.targeted_attempts):
        row = targeted_attempt(
            rng,
            attempt,
            args.targeted_max_word_length,
            args.targeted_steps,
        )
        if row is not None:
            targeted_candidates.append(row)

    def targeted_rank(row: Dict[str, object]):
        state_count = len(row["instance"]["delta"])
        boundary_bound = max(0, state_count - 2)
        return (
            int(row["per_word_budget"]) - boundary_bound,
            int(row["shortest_length"]),
            int(row["per_word_budget"]),
            int(row["lrs"]),
            int(row["steps_done"]),
        )

    targeted_candidates.sort(key=targeted_rank, reverse=True)
    by_budget = sorted(
        targeted_candidates,
        key=lambda row: (
            int(row["per_word_budget"]),
            int(row["shortest_length"]),
            int(row["lrs"]),
            int(row["steps_done"]),
        ),
        reverse=True,
    )
    by_length = sorted(
        targeted_candidates,
        key=lambda row: (
            int(row["shortest_length"]),
            int(row["per_word_budget"]),
            int(row["lrs"]),
            int(row["steps_done"]),
        ),
        reverse=True,
    )
    retained = []
    retained_keys = set()
    seed_pools = (
        by_budget[:1],
        by_length[:1],
        targeted_candidates[:1],
        by_budget,
        by_length,
        targeted_candidates,
    )
    for pool in seed_pools:
        for row in pool:
            key = json.dumps(row["instance"], sort_keys=True)
            if key in retained_keys:
                continue
            retained.append(row)
            retained_keys.add(key)
            if len(retained) >= args.targeted_keep:
                break
        if len(retained) >= args.targeted_keep:
            break
    targeted_rows = [
        complete_targeted_row(row, args.targeted_max_word_length, args.state_cap)
        for row in retained
    ]
    targeted_excess = [
        row["proper_border_analysis"]["budget_excess_over_boundary_bound"]
        for row in targeted_rows
        if row["proper_border_analysis"]["budget_excess_over_boundary_bound"]
        is not None
    ]
    targeted_budget_growth = [
        row["proper_border_analysis"]["exact_budget_growth_vs_normalized_slice"]
        for row in targeted_rows
        if row["proper_border_analysis"]["exact_budget_growth_vs_normalized_slice"]
        is not None
    ]
    targeted_length_growth = [
        row["proper_border_analysis"]["selected_length_minus_normalized_slice"]
        for row in targeted_rows
        if row["proper_border_analysis"]["selected_length_minus_normalized_slice"]
        is not None
    ]

    return {
        "experiment": "A008-shortest-witnesses",
        "scope": "abstract BorderAvoid; exhaustive two-state binary partial instances",
        "limits": {
            "instances_expected": 20736,
            "max_word_length": args.max_word_length,
            "state_cap": args.state_cap,
            "no_witness_necessary_checks": args.no_witness_checks,
            "two_state_scan_length": two_state_scan_length,
            "two_state_exact_shortcut": args.max_word_length >= 1,
            "targeted_seed": args.targeted_seed,
            "targeted_attempts": args.targeted_attempts,
            "targeted_steps": args.targeted_steps,
            "targeted_max_word_length": args.targeted_max_word_length,
            "targeted_keep": args.targeted_keep,
        },
        "counts": {
            "instances_enumerated": total_instances,
            "shortest_witness_instances": len(shortest_rows),
            "no_witness_to_word_cap": len(no_witness_instances),
            "words_checked": total_words_checked,
            "forward_reverse_oracle_comparisons": oracle_comparisons,
            "failures": failures,
            "cut_applicable": cut_applicable,
            "cut_failures": cut_failures,
            "shorter_failure_categories": failure_categories,
            "two_state_n00_status": two_state_status_counts,
            "two_state_n00_state_histogram": two_state_state_histogram,
            "two_state_fallback_instances": fallback_instances,
        },
        "histograms": {
            "shortest_length": length_histogram,
            "lrs": lrs_histogram,
            "per_word_budget": budget_histogram,
        },
        "extrema": {
            "largest_shortest_length": top_by("shortest_length"),
            "largest_lrs": top_by("lrs"),
            "largest_per_word_budget": top_by("per_word_budget"),
            "with_boundary_diagnostics": extremals,
        },
        "no_witness_diagnostics": no_witness_diagnostics,
        "targeted": {
            "attempts": args.targeted_attempts,
            "attempts_with_base_candidates": len(targeted_candidates),
            "rows_retained": len(targeted_rows),
            "rows_with_budget_excess_over_boundary_bound": sum(
                excess > 0 for excess in targeted_excess
            ),
            "largest_budget_excess_over_boundary_bound": (
                max(targeted_excess) if targeted_excess else None
            ),
            "rows_with_budget_growth_vs_normalized_slice": sum(
                growth > 0 for growth in targeted_budget_growth
            ),
            "largest_budget_growth_vs_normalized_slice": (
                max(targeted_budget_growth) if targeted_budget_growth else None
            ),
            "largest_length_growth_over_normalized_slice": (
                max(targeted_length_growth) if targeted_length_growth else None
            ),
            "rows": targeted_rows,
            "interpretation": "Targeted rows preserve a base admissible word while adding flags. Exact instance budgets are reported only when the strong finite search exhausts its graph; otherwise the row remains UNKNOWN.",
        },
        "interpretation": {
            "shortestness": "A returned shortest word has all words through the preceding lengths checked. For two states, no witness after length one uses the exact N''(0,0) shortcut below; capped searches remain UNKNOWN.",
            "cuts": "C008, C009, and the proved visited-state C013 cut are tested on every proper prefix of each shortest witness. Applicable cuts should produce a shorter witness; failures are recorded.",
            "necessary_search": "N'' searches are exact only for their fixed finite graph and budget parameters. A global NO certificate is recorded only for an explicit empty-language reason.",
            "two_state_shortcut": "Each two-state boundary slice has a shortest accepting path of length at most one. Such words have only empty/full borders. Thus N''(0,0) is empty exactly when no witness exists. The census checks this finite encoding space; the binary all-word implication is proved in lean/Subtail/TwoState.lean.",
            "scope": "No result transfers to subtype-derived instances or Problem 1.7.",
        },
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-word-length", type=int, default=12)
    parser.add_argument("--state-cap", type=int, default=200000)
    parser.add_argument("--no-witness-checks", type=int, default=3)
    parser.add_argument("--targeted-seed", type=int, default=8008)
    parser.add_argument("--targeted-attempts", type=int, default=120)
    parser.add_argument("--targeted-steps", type=int, default=16)
    parser.add_argument("--targeted-max-word-length", type=int, default=12)
    parser.add_argument("--targeted-keep", type=int, default=6)
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "results" / "shortest-witnesses.json",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if (
        args.max_word_length < 0
        or args.state_cap < 1
        or args.no_witness_checks < 0
        or args.targeted_attempts < 0
        or args.targeted_steps < 0
        or args.targeted_max_word_length < 0
        or args.targeted_keep < 0
    ):
        raise SystemExit("limits must be non-negative and state cap must be positive")
    result = run_search(args)
    if result["counts"]["failures"] or result["counts"]["cut_failures"]:
        raise AssertionError("shortest-witness checks failed: " + str(result["counts"]))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: result[key] for key in ("experiment", "limits", "counts")}, indent=2, sort_keys=True))
    print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
