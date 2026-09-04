"""Bounded adversarial search for large BorderAvoid budgets.

This experiment targets the abstract BorderAvoid model from Definition 8.1.
It does not claim that generated instances are realizable by subtype
constraints.  A budget is exact only when every split at every lower budget
was exhausted and a split at that budget returned YES.  A cap returns
UNKNOWN.  ``NO_THROUGH`` means only that all requested budgets were exhausted
without a witness.

Run from the repository root, for example:

    python3 experiments/search_budgets.py

The search uses only the standard library and the independent predicates in
``border_lab.py``.  Every returned YES word is checked with both the forward
and reversed direct predicates.
"""

from __future__ import annotations

import argparse
import json
import random
import sys
from pathlib import Path
from typing import Dict, List, Optional, Tuple


ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from experiments.border_lab import (  # noqa: E402
    Instance,
    Sandwich,
    border_witness,
    fixed_word_instance,
    sufficient,
    witness,
    word_budget,
    words,
)


def random_instance(rng: random.Random, states: int) -> Instance:
    """Generate a small partial binary DFA with sparse flags.

    The parameter choices deliberately include complete and partial machines,
    and several flag densities.  A sparse flag set leaves enough accepted
    words for the comparison to have a chance of finding a witness.
    """

    p_undefined = rng.choice((0.02, 0.05, 0.10, 0.16))
    p_flag = rng.choice((0.03, 0.06, 0.10, 0.16, 0.24))
    delta = tuple(
        tuple(
            -1 if rng.random() < p_undefined else rng.randrange(states)
            for _ in range(2)
        )
        for _ in range(states)
    )
    final = frozenset(
        q for q in range(states) if rng.random() < rng.choice((0.20, 0.35, 0.50))
    )
    if not final:
        final = frozenset({rng.randrange(states)})
    bad = frozenset(q for q in range(states) if rng.random() < 0.025)
    flags = frozenset(
        (i, j)
        for i in range(states)
        for j in range(states)
        if rng.random() < p_flag
    )
    return Instance(delta, final, flags, bad)


def encode_instance(instance: Instance) -> Dict[str, object]:
    """Return a JSON-safe complete instance description."""

    return {
        "alphabet": instance.alphabet,
        "start": instance.start,
        "delta": [list(row) for row in instance.delta],
        "final": sorted(instance.final),
        "bad": sorted(instance.bad),
        "flags": [list(pair) for pair in sorted(instance.flags)],
    }


def decode_instance(data: Dict[str, object]) -> Instance:
    """Decode the complete JSON representation emitted by this experiment."""

    return Instance(
        tuple(tuple(row) for row in data["delta"]),
        frozenset(data["final"]),
        frozenset(tuple(pair) for pair in data["flags"]),
        frozenset(data["bad"]),
        int(data["start"]),
        str(data["alphabet"]),
    )


def normalize_trivial_flags(instance: Instance) -> Instance:
    """Remove flag effects that every witness must avoid structurally.

    A diagonal flag rejects every run visiting that state.  A flag from the
    start state to a final state rejects every word ending in that state,
    because the empty suffix is always a prefix.  We encode those two effects
    as ``bad`` and ``final`` restrictions, then drop all flags.  This is a
    diagnostic normalization, not an equivalence theorem for arbitrary
    callers of this module.
    """

    diagonal_bad = frozenset(
        q for q in range(len(instance.delta)) if (q, q) in instance.flags
    )
    empty_blocked_finals = frozenset(
        q for q in instance.final if (instance.start, q) in instance.flags
    )
    return Instance(
        instance.delta,
        instance.final - empty_blocked_finals,
        frozenset(),
        instance.bad | diagonal_bad,
        instance.start,
        instance.alphabet,
    )


def direct_summary(instance: Instance, max_word_length: int) -> Dict[str, object]:
    """Find the first and lowest-budget direct witnesses in a bounded scan."""

    first: Optional[Tuple[str, int]] = None
    best: Optional[Tuple[str, int]] = None
    checked = 0
    for word in words(instance.alphabet, max_word_length):
        checked += 1
        if not witness(instance, word):
            continue
        # This is deliberately independent of the reverse-reading search.
        if not border_witness(instance, word):
            raise AssertionError("forward/reverse direct predicates disagree")
        budget = word_budget(instance, word)
        if budget is None:
            raise AssertionError("word_budget rejected a direct witness")
        if first is None:
            first = (word, budget)
        if best is None or (budget, len(word), word) < (
            best[1],
            len(best[0]),
            best[0],
        ):
            best = (word, budget)
    return {
        "words_checked": checked,
        "first_witness": None
        if first is None
        else {"word": first[0], "word_budget": first[1]},
        "lowest_word_budget_witness": None
        if best is None
        else {"word": best[0], "word_budget": best[1]},
    }


def search_budget(
    instance: Instance, max_budget: int, state_cap: int
) -> Dict[str, object]:
    """Search increasing sufficient budgets with explicit cap semantics."""

    splits_checked = 0
    lower_no_splits = 0
    for budget in range(max_budget + 1):
        for L in range(budget + 1):
            D = budget - L
            splits_checked += 1
            result = Sandwich(instance, L, D, strong=True).search(
                max_states=state_cap
            )
            status = result["status"]
            if status == "YES":
                word = result["word"]
                if not witness(instance, word):
                    raise AssertionError("Sandwich returned a non-witness")
                if not border_witness(instance, word):
                    raise AssertionError("Sandwich word failed border predicate")
                if not sufficient(instance, word, L, D):
                    raise AssertionError("Sandwich word failed sufficient predicate")
                return {
                    "status": "EXACT",
                    "budget": budget,
                    "split": {"L": L, "D": D},
                    "word": word,
                    "word_length": len(word),
                    "search_states": result["states"],
                    "splits_checked": splits_checked,
                    "lower_no_splits": lower_no_splits,
                }
            if status == "UNKNOWN":
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
            if status != "NO":
                raise AssertionError(f"unexpected Sandwich status: {status}")
            lower_no_splits += 1
    return {
        "status": "NO_THROUGH",
        "through_budget": max_budget,
        "splits_checked": splits_checked,
        "lower_no_splits": lower_no_splits,
    }


def compare_instance(
    instance: Instance,
    max_budget: int,
    max_word_length: int,
    state_cap: int,
) -> Dict[str, object]:
    """Compare an instance with its exact matching no-flag baseline."""

    direct = direct_summary(instance, max_word_length)
    flagged = search_budget(instance, max_budget, state_cap)
    baseline_instance = Instance(
        instance.delta,
        instance.final,
        frozenset(),
        instance.bad,
        instance.start,
        instance.alphabet,
    )
    baseline = search_budget(baseline_instance, max_budget, state_cap)
    row: Dict[str, object] = {
        "states": len(instance.delta),
        "instance": encode_instance(instance),
        "direct": direct,
        "flagged": flagged,
        "no_flag_baseline": baseline,
    }
    if flagged.get("status") == "EXACT" and baseline.get("status") == "EXACT":
        row["exact_growth_over_baseline"] = (
            flagged["budget"] - baseline["budget"]
        )
    return row


def replay_stored_examples(path: Path) -> Dict[str, object]:
    """Replay stored exact/growth rows and test trivial-flag normalization.

    This reads an existing compact result file and does not regenerate its
    census.  The replay rechecks the stored witness directly, re-exhausts the
    stored budget prefix, and measures the normalized no-flag baseline.
    """

    data = json.loads(path.read_text())
    limits = data["limits"]
    max_budget = int(limits["max_budget"])
    state_cap = int(limits["sandwich_state_cap"])
    groups = ("top_exact_flagged", "top_growth_over_no_flag")
    seen = set()
    rows: List[Dict[str, object]] = []
    for group in groups:
        for stored in data["results"][group]:
            key = json.dumps(stored["instance"], sort_keys=True)
            if key in seen:
                continue
            seen.add(key)
            instance = decode_instance(stored["instance"])
            flagged = stored["flagged"]
            baseline = stored["no_flag_baseline"]
            if flagged["status"] != "EXACT" or baseline["status"] != "EXACT":
                raise AssertionError("replay source row is not exact")
            flagged_budget = int(flagged["budget"])
            baseline_budget = int(baseline["budget"])
            flagged_word = flagged["word"]
            flagged_split = flagged["split"]
            baseline_word = baseline["word"]
            baseline_split = baseline["split"]
            baseline_instance = Instance(
                instance.delta,
                instance.final,
                frozenset(),
                instance.bad,
                instance.start,
                instance.alphabet,
            )

            # Directly recheck the two stored words before invoking the
            # finite reverse-reading search.
            flagged_direct = {
                "witness": witness(instance, flagged_word),
                "border_witness": border_witness(instance, flagged_word),
                "sufficient": sufficient(
                    instance,
                    flagged_word,
                    int(flagged_split["L"]),
                    int(flagged_split["D"]),
                ),
            }
            baseline_direct = {
                "witness": witness(baseline_instance, baseline_word),
                "border_witness": border_witness(baseline_instance, baseline_word),
                "sufficient": sufficient(
                    baseline_instance,
                    baseline_word,
                    int(baseline_split["L"]),
                    int(baseline_split["D"]),
                ),
            }
            if not all(flagged_direct.values()) or not all(baseline_direct.values()):
                raise AssertionError("stored witness failed replay predicate")

            flagged_replay = search_budget(instance, flagged_budget, state_cap)
            baseline_replay = search_budget(
                baseline_instance, baseline_budget, state_cap
            )
            if (
                flagged_replay.get("status") != "EXACT"
                or flagged_replay.get("budget") != flagged_budget
                or baseline_replay.get("status") != "EXACT"
                or baseline_replay.get("budget") != baseline_budget
            ):
                raise AssertionError("stored exact budget failed replay")

            normalized = normalize_trivial_flags(instance)
            normalized_replay = search_budget(normalized, max_budget, state_cap)
            normalized_budget = normalized_replay.get("budget")
            residual_growth = None
            survives = None
            if normalized_replay.get("status") == "EXACT":
                residual_growth = flagged_budget - int(normalized_budget)
                survives = residual_growth > 0
            rows.append(
                {
                    "generator": stored["generator"],
                    "states": stored["states"],
                    "stored_flagged_budget": flagged_budget,
                    "stored_baseline_budget": baseline_budget,
                    "stored_growth": stored.get("exact_growth_over_baseline"),
                    "flagged_direct_checks": flagged_direct,
                    "baseline_direct_checks": baseline_direct,
                    "flagged_replay_budget": flagged_replay["budget"],
                    "baseline_replay_budget": baseline_replay["budget"],
                    "normalized": {
                        "diagonal_states_added_to_bad": sorted(
                            q
                            for q in range(len(instance.delta))
                            if (q, q) in instance.flags
                        ),
                        "final_states_removed_for_empty_flag": sorted(
                            q
                            for q in instance.final
                            if (instance.start, q) in instance.flags
                        ),
                        "result": normalized_replay,
                        "residual_growth_vs_normalized": residual_growth,
                        "original_growth_survives": survives,
                    },
                }
            )

    return {
        "description": "Independent replay of stored exact and growth examples",
        "source_groups": list(groups),
        "unique_rows": len(rows),
        "limits": {
            "max_budget_for_normalized_search": max_budget,
            "sandwich_state_cap": state_cap,
        },
        "all_checks_passed": True,
        "rows": rows,
    }


def compact_score(row: Dict[str, object]) -> Tuple[int, int, int]:
    """Rank exact rows by budget, then flag growth, then machine size."""

    flagged = row["flagged"]
    baseline = row["no_flag_baseline"]
    budget = flagged.get("budget", -1) if flagged.get("status") == "EXACT" else -1
    growth = row.get("exact_growth_over_baseline", -1)
    if not isinstance(growth, int):
        growth = -1
    return (int(budget), int(growth), int(row["states"]))


def run(args: argparse.Namespace) -> Dict[str, object]:
    rng = random.Random(args.seed)
    rows: List[Dict[str, object]] = []
    exact_rows: List[Dict[str, object]] = []
    growth_rows: List[Dict[str, object]] = []
    target_rows: List[Dict[str, object]] = []
    lower_bound_rows: List[Dict[str, object]] = []
    status_counts = {"EXACT": 0, "NO_THROUGH": 0, "UNKNOWN": 0}
    baseline_status_counts = {"EXACT": 0, "NO_THROUGH": 0, "UNKNOWN": 0}
    splits_checked = 0
    direct_witness_instances = 0

    # Include the previous regular-language baseline as named calibration
    # inputs.  The random search then starts from a reproducible stream.
    calibration = []
    for n in (1, 2, 3, 5, 8, 12):
        instance = fixed_word_instance(n)
        row = compare_instance(
            # Let the named calibration family reach its known n-1 budget,
            # while keeping the random search at the user-selected limit.
            instance,
            max(args.max_budget, n),
            max(args.max_word_length, n),
            args.state_cap,
        )
        row["generator"] = {"kind": "fixed_word_calibration", "n": n}
        calibration.append(row)

    for index in range(args.instances):
        states = rng.randint(args.min_states, args.max_states)
        instance = random_instance(rng, states)
        row = compare_instance(
            instance, args.max_budget, args.max_word_length, args.state_cap
        )
        row["generator"] = {"kind": "seeded_random_partial_dfa", "index": index}
        rows.append(row)

        flagged = row["flagged"]
        baseline = row["no_flag_baseline"]
        status_counts[flagged["status"]] += 1
        baseline_status_counts[baseline["status"]] += 1
        splits_checked += int(flagged.get("splits_checked", 0))
        if direct_summary := row["direct"]:
            if direct_summary["first_witness"] is not None:
                direct_witness_instances += 1
        if flagged.get("status") == "EXACT":
            exact_rows.append(row)
            if row.get("exact_growth_over_baseline", -1) > 0:
                growth_rows.append(row)
            if flagged["budget"] > states:
                target_rows.append(row)
        elif (
            flagged.get("status") == "NO_THROUGH"
            and flagged.get("through_budget", -1) > states
            and row["direct"]["first_witness"] is not None
        ):
            # This is only a bounded lower bound.  The direct scan supplies a
            # validated witness, while every sufficient split through the
            # requested budget was exhausted.
            lower_bound_rows.append(row)

    top_exact = sorted(exact_rows, key=compact_score, reverse=True)[:5]
    top_growth = sorted(growth_rows, key=compact_score, reverse=True)[:5]
    top_targets = sorted(target_rows, key=compact_score, reverse=True)[:5]
    top_lower_bounds = sorted(
        lower_bound_rows,
        key=lambda row: (
            row["flagged"].get("through_budget", -1),
            row["states"],
        ),
        reverse=True,
    )[:5]
    resistant_rows = sorted(
        (
            row
            for row in rows
            if row["flagged"].get("status") != "EXACT"
        ),
        key=lambda row: (
            row["flagged"].get("through_budget", -1),
            row["flagged"].get("first_unknown", {}).get("budget", -1),
            row["states"],
        ),
        reverse=True,
    )[:5]
    unknown_rows = sorted(
        (
            row
            for row in rows
            if row["flagged"].get("status") == "UNKNOWN"
        ),
        key=lambda row: (
            row["flagged"].get("first_unknown", {}).get("budget", -1),
            row["flagged"].get("first_unknown", {}).get("states", -1),
        ),
        reverse=True,
    )[:5]

    return {
        "experiment": "A009-budget-search",
        "description": "Bounded adversarial search over abstract BorderAvoid instances",
        "seed": args.seed,
        "limits": {
            "random_instances": args.instances,
            "states": [args.min_states, args.max_states],
            "max_budget": args.max_budget,
            "max_word_length": args.max_word_length,
            "sandwich_state_cap": args.state_cap,
            "predicate": "strong Sandwich search for S''(L,D)",
        },
        "generator": {
            "random": "partial binary DFA; p_undefined in {0.02,0.05,0.10,0.16}; p_flag in {0.03,0.06,0.10,0.16,0.24}; sparse final and bad sets",
            "calibration": "fixed_word_instance(n) for n in {1,2,3,5,8,12}",
        },
        "counts": {
            "calibration_instances": len(calibration),
            "random_instances": len(rows),
            "random_direct_witness_instances": direct_witness_instances,
            "flagged_statuses": status_counts,
            "baseline_statuses": baseline_status_counts,
            "flagged_splits_checked": splits_checked,
            "exact_flagged_rows": len(exact_rows),
            "positive_exact_growth_rows": len(growth_rows),
            "flagged_budget_greater_than_states": len(target_rows),
            "bounded_lower_bound_rows": len(lower_bound_rows),
        },
        "results": {
            "calibration": calibration,
            "top_exact_flagged": top_exact,
            "top_growth_over_no_flag": top_growth,
            "target_budget_greater_than_states": top_targets,
            "bounded_lower_bound_examples": top_lower_bounds,
            "resistant_examples": resistant_rows,
            "unknown_examples": unknown_rows,
        },
        "interpretation": {
            "exact": "EXACT means every lower (L,D) split was exhausted with NO and the reported split returned YES.",
            "no_through": "NO_THROUGH means all requested budgets were exhausted; it is not a global NO result.",
            "unknown": "UNKNOWN means a finite state cap interrupted a split and cannot be treated as NO.",
            "scope": "All generated instances are abstract BorderAvoid instances. No row establishes a result for SEP or Problem 1.7.",
        },
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seed", type=int, default=2026090409)
    parser.add_argument("--instances", type=int, default=1200)
    parser.add_argument("--min-states", type=int, default=2)
    parser.add_argument("--max-states", type=int, default=8)
    parser.add_argument("--max-budget", type=int, default=8)
    parser.add_argument("--max-word-length", type=int, default=12)
    parser.add_argument("--state-cap", type=int, default=50000)
    parser.add_argument(
        "--replay-stored",
        action="store_true",
        help="replay stored exact/growth rows and update the result file",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=ROOT / "results" / "budget-search.json",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    if args.replay_stored:
        if not args.output.exists():
            raise SystemExit(f"stored result does not exist: {args.output}")
        data = json.loads(args.output.read_text())
        data["replay"] = replay_stored_examples(args.output)
        args.output.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
        print(json.dumps(data["replay"], indent=2, sort_keys=True))
        print(f"updated {args.output}")
        return
    if args.min_states < 1 or args.max_states < args.min_states:
        raise SystemExit("invalid state range")
    if args.instances < 0 or args.max_budget < 0 or args.max_word_length < 0:
        raise SystemExit("limits must be non-negative")
    result = run(args)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({key: result[key] for key in ("experiment", "seed", "limits", "counts")}, indent=2, sort_keys=True))
    print(f"wrote {args.output}")


if __name__ == "__main__":
    main()
