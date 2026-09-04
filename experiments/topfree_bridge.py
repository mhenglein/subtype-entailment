"""Exact regular post-closure for normalized top-free subtype constraints.

This module implements one foundational stage of the memo's reduction.  A
finite set of configurations is closed under the forward propagation machine
W by building a P-automaton for the reverse machine W^rev.  The resulting
epsilon-NFA recognizes, for every variable, exactly the stack words reachable
from the supplied seeds.  It is therefore a regular representation of the
canonical path sets; no depth bound is used.

The module deliberately does not implement the unresolved search for a
separating path.  It does implement exact (automata-theoretic) checks for
normalised constraints, denials, prefix closure, satisfiability from forced
roots, and a supplied canonical countermodel.

Only the Python standard library is used.  Python 3.9+ is required.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from typing import Dict, FrozenSet, Hashable, Iterable, List, Mapping, Optional, Set, Tuple, Union


Word = str
State = Hashable


class _SeedNode:
    """Identity-only NFA node, kept separate from user control states."""

    __slots__ = ("serial",)

    def __init__(self, serial: int):
        self.serial = serial


@dataclass(frozen=True)
class ProductLower:
    """A constraint ``left x right <= target``."""

    left: State
    right: State
    target: State


@dataclass(frozen=True)
class ProductUpper:
    """A constraint ``source <= left x right``."""

    source: State
    left: State
    right: State


@dataclass(frozen=True)
class VariableLeq:
    """A constraint ``source <= target``."""

    source: State
    target: State


@dataclass(frozen=True)
class BottomDenial:
    """A constraint ``source <= bottom``."""

    source: State


Constraint = Union[ProductLower, ProductUpper, VariableLeq, BottomDenial]


@dataclass(frozen=True)
class PDSRule:
    """A pushdown transition.

    ``push`` prepends ``letter`` to the stack; ``pop`` removes it.  The stack
    top is the leftmost letter, matching the memo.
    """

    source: State
    target: State
    operation: str
    letter: Optional[str] = None

    def __post_init__(self) -> None:
        if self.operation not in {"push", "pop", "eps"}:
            raise ValueError(f"unknown operation: {self.operation}")
        if self.operation == "eps" and self.letter is not None:
            raise ValueError("epsilon rules cannot have a letter")
        if self.operation != "eps" and self.letter not in {"0", "1"}:
            raise ValueError("push/pop rules need a binary letter")


class NormalizedSystem:
    """A finite normalized constraint system and its propagation machine W."""

    def __init__(self, constraints: Iterable[Constraint]):
        self.constraints: Tuple[Constraint, ...] = tuple(constraints)
        states: Set[State] = set()
        rules: List[PDSRule] = []
        forced: Set[State] = set()
        denials: Set[State] = set()

        for constraint in self.constraints:
            if isinstance(constraint, ProductLower):
                states.update((constraint.left, constraint.right, constraint.target))
                rules.extend(
                    (
                        PDSRule(constraint.left, constraint.target, "push", "0"),
                        PDSRule(constraint.right, constraint.target, "push", "1"),
                    )
                )
                forced.add(constraint.target)
            elif isinstance(constraint, ProductUpper):
                states.update((constraint.source, constraint.left, constraint.right))
                rules.extend(
                    (
                        PDSRule(constraint.source, constraint.left, "pop", "0"),
                        PDSRule(constraint.source, constraint.right, "pop", "1"),
                    )
                )
            elif isinstance(constraint, VariableLeq):
                states.update((constraint.source, constraint.target))
                rules.append(PDSRule(constraint.source, constraint.target, "eps"))
            elif isinstance(constraint, BottomDenial):
                states.add(constraint.source)
                denials.add(constraint.source)
            else:
                raise TypeError(f"unsupported constraint: {constraint!r}")

        self.states: FrozenSet[State] = frozenset(states)
        self.rules: Tuple[PDSRule, ...] = tuple(rules)
        self.forced_roots: FrozenSet[State] = frozenset(forced)
        self.denials: FrozenSet[State] = frozenset(denials)

    @classmethod
    def from_constraints(cls, constraints: Iterable[Constraint]) -> "NormalizedSystem":
        return cls(constraints)


class EpsilonNFA:
    """A finite epsilon-NFA with hashable states and binary labels."""

    def __init__(self) -> None:
        self.eps: Dict[State, Set[State]] = {}
        self.edges: Dict[State, Dict[str, Set[State]]] = {}
        self.states: Set[State] = set()
        self.final: Set[State] = set()

    def add_state(self, state: State) -> None:
        self.states.add(state)
        self.eps.setdefault(state, set())
        self.edges.setdefault(state, {"0": set(), "1": set()})

    def add_epsilon(self, source: State, target: State) -> bool:
        self.add_state(source)
        self.add_state(target)
        before = len(self.eps[source])
        self.eps[source].add(target)
        return len(self.eps[source]) != before

    def add_edge(self, source: State, letter: str, target: State) -> bool:
        if letter not in {"0", "1"}:
            raise ValueError(f"invalid alphabet letter: {letter}")
        self.add_state(source)
        self.add_state(target)
        before = len(self.edges[source][letter])
        self.edges[source][letter].add(target)
        return len(self.edges[source][letter]) != before

    def epsilon_closure(self, seeds: Iterable[State]) -> FrozenSet[State]:
        closure: Set[State] = set(seeds)
        work = list(closure)
        while work:
            state = work.pop()
            for target in self.eps.get(state, ()):
                if target not in closure:
                    closure.add(target)
                    work.append(target)
        return frozenset(closure)

    def all_epsilon_closures(self) -> Dict[State, FrozenSet[State]]:
        return {state: self.epsilon_closure((state,)) for state in self.states}

    def step_subset(self, subset: Iterable[State], letter: str) -> FrozenSet[State]:
        targets: Set[State] = set()
        for state in subset:
            targets.update(self.edges.get(state, {}).get(letter, ()))
        return self.epsilon_closure(targets)

    def accepts(self, start: State, word: Word) -> bool:
        current = self.epsilon_closure((start,))
        for letter in word:
            current = self.step_subset(current, letter)
            if not current:
                return False
        return bool(current.intersection(self.final))

    def nonempty_from(self, start: State) -> bool:
        """Decide whether the language from ``start`` is nonempty."""
        current = self.epsilon_closure((start,))
        if current.intersection(self.final):
            return True
        seen = set(current)
        queue = deque(current)
        while queue:
            state = queue.popleft()
            for letter in ("0", "1"):
                for target in self.edges.get(state, {}).get(letter, ()):
                    for closed in self.epsilon_closure((target,)):
                        if closed not in seen:
                            seen.add(closed)
                            queue.append(closed)
                    if self.epsilon_closure((target,)).intersection(self.final):
                        return True
        return False


def _reverse_rules(rules: Iterable[PDSRule]) -> Tuple[PDSRule, ...]:
    """Reverse a PDS transition, preserving its concrete operation."""
    reversed_rules: List[PDSRule] = []
    for rule in rules:
        if rule.operation == "push":
            operation = "pop"
        elif rule.operation == "pop":
            operation = "push"
        else:
            operation = "eps"
        reversed_rules.append(PDSRule(rule.target, rule.source, operation, rule.letter))
    return tuple(reversed_rules)


def _add_seed_path(automaton: EpsilonNFA, source: State, word: Word, final: State, serial: int) -> int:
    """Add one source-to-final path, using fresh intermediate states."""
    automaton.add_state(source)
    if not word:
        automaton.add_epsilon(source, final)
        return serial
    current = source
    for index, letter in enumerate(word):
        if index == len(word) - 1:
            target = final
        else:
            target = _SeedNode(serial)
            serial += 1
        automaton.add_edge(current, letter, target)
        current = target
    return serial


def _saturate_pre_star(automaton: EpsilonNFA, rules: Iterable[PDSRule]) -> None:
    """Saturate an NFA for predecessor configurations of a PDS.

    For a rule ``p --pop a--> q``, add ``p -a-> q``.  For a rule
    ``p --push a--> q``, every path ``q -a-> r`` gives ``p -eps-> r``.
    Epsilon rules are added directly.  Epsilon closure is recomputed while
    edges are added, so paths beginning with existing or newly derived
    epsilon edges are handled exactly.
    """
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
                for after_eps in closures.get(rule.target, frozenset()):
                    for destination in automaton.edges.get(after_eps, {}).get(rule.letter, ()):
                        changed = automaton.add_epsilon(rule.source, destination) or changed


class ReachablePathSets:
    """Exact regular path sets generated by a finite family of seed paths."""

    def __init__(self, system: NormalizedSystem, seeds: Iterable[Tuple[State, Word]]):
        self.system = system
        self.seeds: Tuple[Tuple[State, Word], ...] = tuple(seeds)
        self.final = object()
        self.automaton = EpsilonNFA()
        self.automaton.add_state(self.final)
        serial = 0
        for source, word in self.seeds:
            serial = _add_seed_path(self.automaton, source, word, self.final, serial)
        _saturate_pre_star(self.automaton, _reverse_rules(system.rules))
        self.automaton.final.add(self.final)

    def contains(self, variable: State, word: Word) -> bool:
        return self.automaton.accepts(variable, word)

    def nonempty(self, variable: State) -> bool:
        return self.automaton.nonempty_from(variable)

    def _start(self, variable: State) -> FrozenSet[State]:
        return self.automaton.epsilon_closure((variable,))

    def _after(self, variable: State, letter: str) -> FrozenSet[State]:
        return self.automaton.step_subset(self._start(variable), letter)

    def included(self, source_start: Iterable[State], target_start: Iterable[State]) -> bool:
        """Decide inclusion between two regular languages in this NFA."""
        source = self.automaton.epsilon_closure(source_start)
        target = self.automaton.epsilon_closure(target_start)
        pending = deque([(source, target)])
        seen = {(source, target)}
        while pending:
            left, right = pending.popleft()
            if left.intersection(self.automaton.final) and not right.intersection(self.automaton.final):
                return False
            for letter in ("0", "1"):
                next_left = self.automaton.step_subset(left, letter)
                next_right = self.automaton.step_subset(right, letter)
                pair = (next_left, next_right)
                if pair not in seen:
                    seen.add(pair)
                    pending.append(pair)
        return True

    def included_variables(self, source: State, target: State) -> bool:
        return self.included(self._start(source), self._start(target))

    def prefixed_included(self, source: State, letter: str, target: State) -> bool:
        """Decide ``letter . L(source) <= L(target)``."""
        return self.included(self._start(source), self._after(target, letter))

    def quotient_included(self, source: State, letter: str, target: State) -> bool:
        """Decide ``L(source) / letter <= L(target)``."""
        return self.included(self._after(source, letter), self._start(target))

    def prefix_closed(self, variables: Optional[Iterable[State]] = None) -> bool:
        """Check prefix closure exactly on the subset-state graph.

        A non-accepting prefix is a violation precisely when its reachable
        subset state has an accepting descendant.  This avoids confusing
        left quotients (used by product upper bounds) with removal of a final
        letter, which is the operation relevant to prefix closure.
        """
        variables_tuple = tuple(self.system.states if variables is None else variables)
        for variable in variables_tuple:
            start = self._start(variable)
            pending = deque([start])
            seen = {start}
            graph: Dict[FrozenSet[State], Tuple[FrozenSet[State], ...]] = {}
            while pending:
                subset = pending.popleft()
                successors = []
                for letter in ("0", "1"):
                    successor = self.automaton.step_subset(subset, letter)
                    successors.append(successor)
                    if successor not in seen:
                        seen.add(successor)
                        pending.append(successor)
                graph[subset] = tuple(successors)

            accepting = {
                subset for subset in seen if subset.intersection(self.automaton.final)
            }
            can_reach_accepting = set(accepting)
            changed = True
            while changed:
                changed = False
                for subset, successors in graph.items():
                    if subset not in can_reach_accepting and any(
                        successor in can_reach_accepting for successor in successors
                    ):
                        can_reach_accepting.add(subset)
                        changed = True
            if any(
                subset in can_reach_accepting
                and not subset.intersection(self.automaton.final)
                for subset in seen
            ):
                return False
        return True

    def as_finite_automaton_data(self) -> Mapping[str, object]:
        """Return compact, non-semantic diagnostics for reproducible reports."""
        return {
            "nfa_states": len(self.automaton.states),
            "epsilon_edges": sum(len(targets) for targets in self.automaton.eps.values()),
            "letter_edges": sum(
                len(targets)
                for by_letter in self.automaton.edges.values()
                for targets in by_letter.values()
            ),
            "seed_count": len(self.seeds),
        }


def forced_root_closure(system: NormalizedSystem) -> ReachablePathSets:
    """Compute the least solution's path sets from unconditional product facts."""
    return ReachablePathSets(system, ((state, "") for state in sorted(system.forced_roots, key=repr)))


def is_satisfiable(system: NormalizedSystem) -> bool:
    """Decide satisfiability using exact forced-root reachability."""
    closure = forced_root_closure(system)
    return not any(closure.nonempty(denial) for denial in system.denials)


def constraint_errors(system: NormalizedSystem, model: ReachablePathSets) -> List[str]:
    """Return exact regular-language violations of normalized constraints."""
    errors: List[str] = []
    for constraint in system.constraints:
        if isinstance(constraint, ProductLower):
            if not model.contains(constraint.target, ""):
                errors.append(f"missing forced root: {constraint.target!r}")
            if not model.prefixed_included(constraint.left, "0", constraint.target):
                errors.append(f"push inclusion failed: 0 {constraint.left!r} <= {constraint.target!r}")
            if not model.prefixed_included(constraint.right, "1", constraint.target):
                errors.append(f"push inclusion failed: 1 {constraint.right!r} <= {constraint.target!r}")
        elif isinstance(constraint, ProductUpper):
            if not model.quotient_included(constraint.source, "0", constraint.left):
                errors.append(f"pop inclusion failed: {constraint.source!r}/0 <= {constraint.left!r}")
            if not model.quotient_included(constraint.source, "1", constraint.right):
                errors.append(f"pop inclusion failed: {constraint.source!r}/1 <= {constraint.right!r}")
        elif isinstance(constraint, VariableLeq):
            if not model.included_variables(constraint.source, constraint.target):
                errors.append(f"variable inclusion failed: {constraint.source!r} <= {constraint.target!r}")
        elif isinstance(constraint, BottomDenial):
            if model.nonempty(constraint.source):
                errors.append(f"denial reached: {constraint.source!r} <= bottom")
    return errors


@dataclass(frozen=True)
class CountermodelResult:
    """Result of constructing a supplied-path canonical countermodel."""

    status: str
    reason: str
    model: Optional[ReachablePathSets] = None
    errors: Tuple[str, ...] = ()


def canonical_countermodel(
    system: NormalizedSystem, alpha: State, beta: State, path: Word
) -> CountermodelResult:
    """Construct and validate the memo's canonical model for a proposed path.

    The alpha seed is every prefix of ``path``.  Forced product roots are added
    separately.  ``status == 'YES'`` means the returned regular path sets are
    an exact countermodel for ``alpha <= beta``.  ``'UNSAT'`` means the input
    constraints have no model.  ``'REJECTED_PATH'`` means only that this
    supplied path failed to produce a countermodel; it is not an entailment
    decision.
    """
    if not is_satisfiable(system):
        return CountermodelResult("UNSAT", "constraint system is unsatisfiable")

    seeds = [(alpha, path[:index]) for index in range(len(path) + 1)]
    seeds.extend((state, "") for state in sorted(system.forced_roots, key=repr))
    model = ReachablePathSets(system, seeds)
    errors = tuple(constraint_errors(system, model))
    if errors:
        return CountermodelResult("REJECTED_PATH", "canonical closure violates constraints", model, errors)
    if not model.prefix_closed((*system.states, alpha, beta)):
        return CountermodelResult("REJECTED_PATH", "canonical closure is not prefix-closed", model)
    if not model.contains(alpha, path):
        return CountermodelResult("REJECTED_PATH", "alpha seed did not survive closure", model)
    if model.contains(beta, path):
        return CountermodelResult("REJECTED_PATH", "beta contains the proposed separating path", model)
    return CountermodelResult("YES", "validated regular countermodel", model)


def finite_reachable_prefixes(
    system: NormalizedSystem,
    seeds: Iterable[Tuple[State, Word]],
    max_depth: int,
) -> Set[Tuple[State, Word]]:
    """Bounded diagnostic closure, useful only for testing the exact NFA.

    This helper is intentionally marked as diagnostic.  It never participates
    in satisfiability or countermodel decisions.
    """
    if max_depth < 0:
        raise ValueError("max_depth must be nonnegative")
    pending = deque((state, word) for state, word in seeds if len(word) <= max_depth)
    seen = set(pending)
    while pending:
        state, word = pending.popleft()
        for rule in system.rules:
            if rule.source != state:
                continue
            if rule.operation == "eps":
                successor = (rule.target, word)
            elif rule.operation == "push":
                successor = (rule.target, rule.letter + word)
            elif word.startswith(rule.letter):
                successor = (rule.target, word[1:])
            else:
                continue
            if len(successor[1]) <= max_depth and successor not in seen:
                seen.add(successor)
                pending.append(successor)
    return seen
