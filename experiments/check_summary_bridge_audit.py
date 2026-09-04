"""Independent bounded audit of the summary bridge.

This file deliberately keeps its direct PDS searches separate from the
summary implementation.  The searches have explicit finite caps, so a
bounded mismatch is meaningful but a bounded match is not an all-length
proof.
"""

from __future__ import annotations

import json
import random
from collections import deque
from pathlib import Path
from typing import Iterable, Optional, Sequence, Tuple

from border_lab import border_witness, witness, words
from summary_bridge import (
    NormalizedSystem,
    ProductLower,
    ProductUpper,
    VariableLeq,
    _denial_predecessor_nfa,
    _subset_after,
    build_pop_summary,
    build_summary_bridge,
    is_satisfiable,
    pop_contains,
)
from topfree_bridge import BottomDenial, PDSRule, canonical_countermodel


def direct_reaches(
    rules: Sequence[PDSRule],
    source,
    word: str,
    target,
    *,
    max_seen: int = 10_000,
) -> Optional[bool]:
    """Bounded direct check for ``<source,word> ->* <target,epsilon>``."""
    seen = {(source, word)}
    pending = deque([(source, word)])
    pruned = False
    while pending:
        state, stack = pending.popleft()
        if state == target and not stack:
            return True
        for rule in rules:
            if rule.source != state:
                continue
            if rule.operation == "eps":
                next_stack = stack
            elif rule.operation == "push":
                next_stack = rule.letter + stack
            elif stack.startswith(rule.letter):
                next_stack = stack[1:]
            else:
                continue
            # The cap is intentionally relative to the queried input.
            if len(next_stack) <= len(word) + 5:
                successor = (rule.target, next_stack)
                if successor not in seen:
                    if len(seen) >= max_seen:
                        pruned = True
                    else:
                        seen.add(successor)
                        pending.append(successor)
            else:
                pruned = True
    return None if pruned else False


def direct_denial_reaches(
    rules: Sequence[PDSRule],
    source,
    word: str,
    denials: Iterable,
    *,
    max_steps: int = 250,
    max_stack: int = 10,
) -> Optional[bool]:
    """Bounded direct check for reaching any denial with any residual stack."""
    denial_set = set(denials)
    seen = {(source, word)}
    pending = deque([(source, word, 0)])
    pruned = False
    while pending:
        state, stack, depth = pending.popleft()
        if state in denial_set:
            return True
        if depth >= max_steps:
            if any(
                rule.source == state
                and (
                    rule.operation != "pop"
                    or stack.startswith(rule.letter)
                )
                for rule in rules
            ):
                pruned = True
            continue
        for rule in rules:
            if rule.source != state:
                continue
            if rule.operation == "eps":
                next_stack = stack
            elif rule.operation == "push":
                next_stack = rule.letter + stack
            elif stack.startswith(rule.letter):
                next_stack = stack[1:]
            else:
                continue
            if len(next_stack) <= max_stack:
                successor = (rule.target, next_stack)
                if successor not in seen:
                    seen.add(successor)
                    pending.append((rule.target, next_stack, depth + 1))
            else:
                pruned = True
    return None if pruned else False


def check_generator_input() -> None:
    rules = [
        PDSRule("start", "mid", "push", "0"),
        PDSRule("mid", "finish", "pop", "0"),
    ]
    summary = build_pop_summary((rule for rule in rules), ("start", "mid", "finish"))
    assert pop_contains(summary, "start", "finish", "")


def check_pop_summaries() -> Tuple[int, int, int]:
    rng = random.Random(20260904)
    attempts = 0
    known = 0
    unknown = 0
    for _ in range(300):
        states = tuple(range(rng.randint(1, 5)))
        rules = []
        for _ in range(rng.randrange(0, 13)):
            operation = rng.choice(("eps", "push", "pop"))
            letter = None if operation == "eps" else rng.choice("01")
            rules.append(
                PDSRule(rng.choice(states), rng.choice(states), operation, letter)
            )
        summary = build_pop_summary(rules, states)
        for source in states:
            for target in states:
                for length in range(5):
                    for number in range(1 << length):
                        stack = format(number, f"0{length}b") if length else ""
                        expected = direct_reaches(rules, source, stack, target)
                        actual = pop_contains(summary, source, target, stack)
                        attempts += 1
                        if expected is None:
                            unknown += 1
                            continue
                        known += 1
                        if expected != actual:
                            raise AssertionError(
                                "Pop mismatch: "
                                f"source={source!r}, target={target!r}, stack={stack!r}"
                            )
    return attempts, known, unknown


def check_s_monitor() -> Tuple[int, int, int]:
    """Compare the denial predecessor monitor with bounded direct runs."""
    rng = random.Random(20260904)
    attempts = 0
    known = 0
    unknown = 0
    for _ in range(400):
        states = tuple(range(rng.randint(1, 4)))
        constraints = []
        for _ in range(rng.randrange(0, 10)):
            kind = rng.randrange(4)
            if kind == 0:
                constraints.append(
                    ProductLower(*[rng.choice(states) for _ in range(3)])
                )
            elif kind == 1:
                constraints.append(
                    ProductUpper(*[rng.choice(states) for _ in range(3)])
                )
            elif kind == 2:
                constraints.append(
                    VariableLeq(rng.choice(states), rng.choice(states))
                )
            else:
                constraints.append(BottomDenial(rng.choice(states)))
        system = NormalizedSystem(constraints)
        alpha = rng.choice(states)
        monitor = _denial_predecessor_nfa(system, states)
        for stack in words("01", 4):
            actual = bool(_subset_after(monitor, alpha, stack) & monitor.final)
            expected = direct_denial_reaches(
                system.rules,
                alpha,
                stack,
                system.denials,
            )
            attempts += 1
            if expected is None:
                unknown += 1
                continue
            known += 1
            if actual != expected:
                raise AssertionError(f"S mismatch for stack {stack!r}: {actual} != {expected}")
    return attempts, known, unknown


def random_system(rng: random.Random) -> Tuple[NormalizedSystem, Tuple[int, ...]]:
    states = tuple(range(rng.randint(1, 5)))
    constraints = []
    for _ in range(rng.randrange(0, 11)):
        kind = rng.randrange(4)
        if kind == 0:
            constraints.append(
                ProductLower(*[rng.choice(states) for _ in range(3)])
            )
        elif kind == 1:
            constraints.append(
                ProductUpper(*[rng.choice(states) for _ in range(3)])
            )
        elif kind == 2:
            constraints.append(
                VariableLeq(rng.choice(states), rng.choice(states))
            )
        else:
            constraints.append(BottomDenial(rng.choice(states)))
    return NormalizedSystem(constraints), states


def check_summary_against_canonical() -> Tuple[int, int, int]:
    rng = random.Random(222)
    cases = 0
    comparisons = 0
    absent_query_cases = 0
    for _ in range(400):
        system, states = random_system(rng)
        if not is_satisfiable(system):
            continue
        alpha = rng.choice(states + ("absent-alpha",))
        beta = rng.choice(states + ("absent-beta",))
        if alpha not in system.states or beta not in system.states:
            absent_query_cases += 1
        bridge = build_summary_bridge(system, alpha, beta)
        cases += 1
        for stack in words("01", 6):
            summary_answer = witness(bridge.instance, stack)
            canonical_answer = canonical_countermodel(
                system, alpha, beta, stack
            ).status == "YES"
            if summary_answer != border_witness(bridge.instance, stack):
                raise AssertionError(f"reversal mismatch for {stack!r}")
            if summary_answer != canonical_answer:
                raise AssertionError(
                    f"summary/canonical mismatch for {stack!r}: "
                    f"{summary_answer} != {canonical_answer}"
                )
            comparisons += 1
    return cases, comparisons, absent_query_cases


def check_unsat_and_empty_query() -> None:
    unsatisfiable = NormalizedSystem(
        (ProductLower("a", "b", "forced"), BottomDenial("forced"))
    )
    try:
        build_summary_bridge(unsatisfiable, "a", "b")
    except ValueError as error:
        assert "unsatisfiable" in str(error)
    else:
        raise AssertionError("unsatisfiable bridge construction was accepted")

    empty = build_summary_bridge(NormalizedSystem(()), "missing-alpha", "missing-beta")
    assert empty.states == ("missing-alpha", "missing-beta")
    assert empty.instance.run("") == (0,)


def main() -> None:
    check_generator_input()
    pop_attempts, pop_known, pop_unknown = check_pop_summaries()
    s_attempts, s_known, s_unknown = check_s_monitor()
    summary_cases, summary_checks, absent_query_cases = check_summary_against_canonical()
    check_unsat_and_empty_query()
    result = {
        "status": "PASS",
        "scope": "independent bounded audit of Pop summaries, S monitor, and summary/canonical bridge",
        "seeds": {"pop": 20260904, "s_monitor": 20260904, "summary": 222},
        "caps": {
            "pop_trials": 300,
            "pop_word_length": 4,
            "pop_stack_length": "word_length + 5",
            "pop_max_seen": 10000,
            "s_trials": 400,
            "s_word_length": 4,
            "s_max_steps": 250,
            "s_max_stack": 10,
            "summary_trials": 400,
            "summary_word_length": 6,
        },
        "counts": {
            "pop_membership_attempts": pop_attempts,
            "pop_known_comparisons": pop_known,
            "pop_unknown": pop_unknown,
            "s_monitor_attempts": s_attempts,
            "s_known_comparisons": s_known,
            "s_unknown": s_unknown,
            "summary_satisfiable_cases": summary_cases,
            "summary_canonical_comparisons": summary_checks,
            "summary_cases_with_absent_query_variable": absent_query_cases,
        },
        "checks": {
            "generator_rule_input": "validated",
            "unsatisfiable_precondition": "validated",
            "absent_query_variables": "validated",
            "empty_and_full_border_reversal": "validated",
        },
        "global_claim": "bounded evidence only; no decision procedure or all-length proof",
    }
    output = Path(__file__).resolve().parents[1] / "results" / "summary-bridge-audit.json"
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
