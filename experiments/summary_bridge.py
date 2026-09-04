"""DFA summary classes for actual normalized top-free propagation systems.

This module implements the finite summary layer behind Sections 4--5 of the
memo.  For a pushdown system ``P``, ``Pop_P(p, q)`` is the language of stack
words ``w`` for which ``<p, w>`` can reach ``<q, epsilon>``.  A finite NFA on
control states recognizes this language.  Push rules are compiled into
epsilon edges whenever the pushed symbol can be consumed by a pop-summary
path; saturation repeats this until a fixed point.

For a query ``alpha <= beta`` we build summaries for ``W`` and
``A = W^rev``.  After reading a prefix ``u``:

* ``B(u) = {q : u in Pop_W(alpha, q)}``;
* ``A(u) = {q : u in Pop_A(beta, q)}``.

The actual flag relation is then
``G(c_i, c_j) iff B(u_i) intersects A(u_j)``.  The returned
``border_lab.Instance`` retains empty subset classes, computes the forced-root
condition (F) as its final-state predicate, and computes the denial condition
(S) as a bad-state predicate using an exact predecessor NFA.

This is a summary construction, not a decision procedure for Problem 1.7.
It has no bounded-stack approximation.  The remaining global difficulty is
the unbounded search for a word avoiding all flagged borders.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from typing import Dict, FrozenSet, Hashable, Iterable, List, Optional, Set, Tuple

try:  # Support both ``python experiments/check_summary_bridge.py`` and imports.
    from .border_lab import Instance
    from .topfree_bridge import (
        BottomDenial,
        NormalizedSystem,
        PDSRule,
        ProductLower,
        ProductUpper,
        VariableLeq,
        is_satisfiable,
    )
except ImportError:  # pragma: no cover - exercised by the script entry point.
    from border_lab import Instance
    from topfree_bridge import (
        BottomDenial,
        NormalizedSystem,
        PDSRule,
        ProductLower,
        ProductUpper,
        VariableLeq,
        is_satisfiable,
    )


State = Hashable
ControlSubset = FrozenSet[State]


class _InternalFinal:
    """Identity-only accepting node for auxiliary NFAs."""


class _NFA:
    """Small epsilon-NFA implementation used by both summary constructions."""

    def __init__(self, states: Iterable[State] = ()):
        self.states: Set[State] = set(states)
        self.eps: Dict[State, Set[State]] = {}
        self.edges: Dict[State, Dict[str, Set[State]]] = {}
        self.final: Set[State] = set()
        for state in self.states:
            self._init_state(state)

    def _init_state(self, state: State) -> None:
        self.states.add(state)
        self.eps.setdefault(state, set())
        self.edges.setdefault(state, {"0": set(), "1": set()})

    def add_epsilon(self, source: State, target: State) -> bool:
        self._init_state(source)
        self._init_state(target)
        before = len(self.eps[source])
        self.eps[source].add(target)
        return len(self.eps[source]) != before

    def add_edge(self, source: State, letter: str, target: State) -> bool:
        if letter not in {"0", "1"}:
            raise ValueError(f"invalid binary letter: {letter}")
        self._init_state(source)
        self._init_state(target)
        before = len(self.edges[source][letter])
        self.edges[source][letter].add(target)
        return len(self.edges[source][letter]) != before

    def epsilon_closure(self, seeds: Iterable[State]) -> FrozenSet[State]:
        closure: Set[State] = set(seeds)
        pending = list(closure)
        while pending:
            state = pending.pop()
            for target in self.eps.get(state, ()):
                if target not in closure:
                    closure.add(target)
                    pending.append(target)
        return frozenset(closure)

    def all_epsilon_closures(self) -> Dict[State, FrozenSet[State]]:
        return {state: self.epsilon_closure((state,)) for state in self.states}

    def step_subset(self, subset: Iterable[State], letter: str) -> FrozenSet[State]:
        targets: Set[State] = set()
        for state in subset:
            targets.update(self.edges.get(state, {}).get(letter, ()))
        return self.epsilon_closure(targets)


def _reverse_rules(rules: Iterable[PDSRule]) -> Tuple[PDSRule, ...]:
    result = []
    for rule in rules:
        if rule.operation == "push":
            operation = "pop"
        elif rule.operation == "pop":
            operation = "push"
        else:
            operation = "eps"
        result.append(PDSRule(rule.target, rule.source, operation, rule.letter))
    return tuple(result)


def _saturate_pre_star(automaton: _NFA, rules: Iterable[PDSRule]) -> None:
    """Compute the standard P-automaton predecessor saturation."""
    rules_tuple = tuple(rules)
    changed = True
    while changed:
        changed = False
        closures = automaton.all_epsilon_closures()
        for rule in rules_tuple:
            if rule.operation == "eps":
                changed = automaton.add_epsilon(rule.source, rule.target) or changed
            elif rule.operation == "pop":
                changed = automaton.add_edge(rule.source, rule.letter, rule.target) or changed
            else:
                # A push p --push a--> q has predecessor edge p -eps-> r
                # whenever q --eps* a eps*--> r is already represented.
                for after_eps in closures.get(rule.target, frozenset()):
                    for destination in automaton.edges.get(after_eps, {}).get(rule.letter, ()):
                        changed = automaton.add_epsilon(rule.source, destination) or changed


def build_pop_summary(rules: Iterable[PDSRule], states: Iterable[State]) -> _NFA:
    """Build an NFA for ``Pop_P(p, q)`` for every pair of controls.

    The base graph has epsilon rules and pop edges.  For each push
    ``p --push a--> q`` we add an epsilon edge ``p -> r`` whenever the current
    graph has a path ``q --eps* a eps*--> r``.  Iteration computes the least
    fixed point.  An NFA path labelled ``w`` from ``p`` to ``q`` is then a
    balanced run from ``<p,w>`` to ``<q,epsilon>``.
    """
    rules_tuple = tuple(rules)
    automaton = _NFA(states)
    for rule in rules_tuple:
        if rule.operation == "eps":
            automaton.add_epsilon(rule.source, rule.target)
        elif rule.operation == "pop":
            automaton.add_edge(rule.source, rule.letter, rule.target)

    push_rules = tuple(rule for rule in rules_tuple if rule.operation == "push")
    changed = True
    while changed:
        changed = False
        closures = automaton.all_epsilon_closures()
        for rule in push_rules:
            for after_eps in closures.get(rule.target, frozenset()):
                for destination in automaton.edges.get(after_eps, {}).get(rule.letter, ()):
                    changed = automaton.add_epsilon(rule.source, destination) or changed
    return automaton


def _subset_after(automaton: _NFA, start: State, word: str) -> FrozenSet[State]:
    current = automaton.epsilon_closure((start,))
    for letter in word:
        current = automaton.step_subset(current, letter)
    return current


def pop_contains(automaton: _NFA, source: State, target: State, word: str) -> bool:
    """Test ``word in Pop_P(source, target)`` in the saturated summary NFA."""
    return target in _subset_after(automaton, source, word)


def _denial_predecessor_nfa(system: NormalizedSystem, states: Iterable[State]) -> _NFA:
    """Recognize ``{w : <q,w> ->*_W <delta,z>}`` for denial states delta."""
    final = _InternalFinal()
    automaton = _NFA(tuple(states) + (final,))
    # A denial target accepts every residual stack word.
    automaton.add_edge(final, "0", final)
    automaton.add_edge(final, "1", final)
    automaton.final = {final}
    for denial in system.denials:
        automaton.add_epsilon(denial, final)
    _saturate_pre_star(automaton, system.rules)
    return automaton


@dataclass(frozen=True)
class SummaryClass:
    """One deterministic class after reading a prefix."""

    b_states: ControlSubset
    a_states: ControlSubset
    s_states: FrozenSet[State]


@dataclass(frozen=True)
class SummaryBridge:
    """Actual subtype-derived summaries and their BorderAvoid instance."""

    system: NormalizedSystem
    alpha: State
    beta: State
    states: Tuple[State, ...]
    w_pop: _NFA
    a_pop: _NFA
    s_bad: _NFA
    classes: Tuple[SummaryClass, ...]
    delta: Tuple[Tuple[int, int], ...]
    start: int
    final: FrozenSet[int]
    bad: FrozenSet[int]
    flags: FrozenSet[Tuple[int, int]]
    instance: Instance

    def class_for(self, word: str) -> int:
        state = self.start
        for letter in word:
            state = self.delta[state][int(letter)]
        return state

    def flag(self, left: int, right: int) -> bool:
        return (left, right) in self.flags

    def pop_w_endpoints(self, word: str) -> FrozenSet[State]:
        return frozenset(q for q in self.states if pop_contains(self.w_pop, self.alpha, q, word))

    def pop_a_endpoints(self, word: str) -> FrozenSet[State]:
        return frozenset(q for q in self.states if pop_contains(self.a_pop, self.beta, q, word))


def build_summary_bridge(
    system: NormalizedSystem, alpha: State, beta: State
) -> SummaryBridge:
    """Build exact actual-summary classes and all sound S/F annotations."""
    if not is_satisfiable(system):
        raise ValueError(
            "cannot build a BorderAvoid instance for an unsatisfiable constraint system"
        )
    states = tuple(sorted(set(system.states) | {alpha, beta}, key=repr))
    w_rules = tuple(system.rules)
    a_rules = _reverse_rules(w_rules)
    w_pop = build_pop_summary(w_rules, states)
    a_pop = build_pop_summary(a_rules, states)
    s_bad = _denial_predecessor_nfa(system, states)

    start_class = SummaryClass(
        frozenset(w_pop.epsilon_closure((alpha,)).intersection(states)),
        frozenset(a_pop.epsilon_closure((beta,)).intersection(states)),
        s_bad.epsilon_closure((alpha,)),
    )
    classes: List[SummaryClass] = [start_class]
    class_ids = {start_class: 0}
    delta_rows: List[List[int]] = []
    pending = deque([start_class])
    while pending:
        current = pending.popleft()
        row: List[int] = []
        for letter in ("0", "1"):
            next_class = SummaryClass(
                frozenset(w_pop.step_subset(current.b_states, letter).intersection(states)),
                frozenset(a_pop.step_subset(current.a_states, letter).intersection(states)),
                s_bad.step_subset(current.s_states, letter),
            )
            target = class_ids.get(next_class)
            if target is None:
                target = len(classes)
                class_ids[next_class] = target
                classes.append(next_class)
                pending.append(next_class)
            row.append(target)
        delta_rows.append(row)

    # Every queued class is processed exactly once, so rows align with IDs.
    delta = tuple((row[0], row[1]) for row in delta_rows)
    forced = system.forced_roots
    final = frozenset(
        index
        for index, state in enumerate(classes)
        if not state.a_states.intersection(forced)
    )
    bad = frozenset(
        index for index, state in enumerate(classes) if any(node in s_bad.final for node in state.s_states)
    )
    flags = frozenset(
        (left, right)
        for left, left_class in enumerate(classes)
        for right, right_class in enumerate(classes)
        if left_class.b_states.intersection(right_class.a_states)
    )
    instance = Instance(delta, final, flags, bad, start=0)
    return SummaryBridge(
        system=system,
        alpha=alpha,
        beta=beta,
        states=states,
        w_pop=w_pop,
        a_pop=a_pop,
        s_bad=s_bad,
        classes=tuple(classes),
        delta=delta,
        start=0,
        final=final,
        bad=bad,
        flags=flags,
        instance=instance,
    )


def summary_diagnostics(bridge: SummaryBridge) -> Dict[str, int]:
    """Return finite construction sizes for a reproducible report."""
    return {
        "control_states": len(bridge.states),
        "w_pop_eps_edges": sum(len(targets) for targets in bridge.w_pop.eps.values()),
        "w_pop_letter_edges": sum(
            len(targets)
            for by_letter in bridge.w_pop.edges.values()
            for targets in by_letter.values()
        ),
        "a_pop_eps_edges": sum(len(targets) for targets in bridge.a_pop.eps.values()),
        "a_pop_letter_edges": sum(
            len(targets)
            for by_letter in bridge.a_pop.edges.values()
            for targets in by_letter.values()
        ),
        "summary_classes": len(bridge.classes),
        "flag_pairs": len(bridge.flags),
        "bad_classes": len(bridge.bad),
        "final_classes": len(bridge.final),
    }
