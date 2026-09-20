"""Effective regular countermodels for bottom/product constraints.

This is an ordinary Python implementation of manuscript Proposition 12.2,
not a Lean-verified extractor. With no resource cap, `extract` terminates on
every non-entailed input. On other inputs its fair word search may continue
forever; callers must first decide non-entailment or impose a resource cap.
Returned graphs still need the independent original-input certificate check.
"""
from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from itertools import count, product
import time


def check_time(deadline):
    if deadline is not None and time.monotonic() >= deadline:
        raise TimeoutError('countermodel extraction time limit')


def bits(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask ^= low


@dataclass
class System:
    size: int
    epsilon: set[tuple[int, int]]
    push: set[tuple[int, int, int]]  # source, letter, target
    pop: set[tuple[int, int, int]]
    forced: set[int]
    denied: set[int]
    left: int
    right: int

    def reverse(self):
        return System(self.size, {(q, p) for p, q in self.epsilon},
                      {(q, a, p) for p, a, q in self.pop},
                      {(q, a, p) for p, a, q in self.push},
                      set(), set(), self.left, self.right)


def normalize(problem, deadline=None):
    """Exact DAG naming; original variables occupy the first slots."""
    ids = {('var', i): i for i in range(len(problem.variables))}
    epsilon, push, pop, forced, denied = set(), set(), set(), set(), set()

    def name(e):
        check_time(deadline)
        if e in ids:
            return ids[e]
        if e[0] == 'prod':
            l, r = name(e[1]), name(e[2])
        q = len(ids)
        ids[e] = q
        if e[0] == 'bot':
            denied.add(q)
        else:
            forced.add(q)
            pop.update(((q, 0, l), (q, 1, r)))
            push.update(((l, 0, q), (r, 1, q)))
        return q

    for s, t in problem.constraints:
        epsilon.add((name(s), name(t)))
    left, right = name(problem.query[0]), name(problem.query[1])
    return System(len(ids), epsilon, push, pop, forced, denied, left, right)


def transitive_closure(rows, deadline=None):
    for k in range(len(rows)):
        check_time(deadline)
        bit, successors = 1 << k, rows[k]
        for p in range(len(rows)):
            if rows[p] & bit:
                rows[p] |= successors


def balanced(system, deadline=None):
    """Least reflexive/epsilon, transitive, push-balanced-pop relation."""
    rows = [1 << p for p in range(system.size)]
    for p, q in system.epsilon:
        rows[p] |= 1 << q
    pops = [[], []]
    for s, a, q in sorted(system.pop):
        pops[a].append((s, q))
    while True:
        check_time(deadline)
        old = rows[:]
        transitive_closure(rows, deadline)
        for p, a, r in sorted(system.push):
            check_time(deadline)
            for s, q in pops[a]:
                if rows[r] & (1 << s):
                    rows[p] |= 1 << q
        if rows == old:
            return rows


class PopMachine:
    def __init__(self, system, deadline=None):
        self.system = system
        self.balanced = balanced(system, deadline)
        self.steps = [[0] * system.size for _ in (0, 1)]
        for p, a, r in system.pop:
            self.steps[a][p] |= self.balanced[r]

    def step(self, states, letter):
        result = 0
        for p in bits(states):
            result |= self.steps[letter][p]
        return result

    def run(self, start, word):
        states = self.balanced[start]
        for a in word:
            states = self.step(states, a)
        return states


class ClosureNFA:
    """From control q, accept exactly the canonical product addresses at q.

    Control states have reverse-balanced epsilon edges and reverse-pop letter
    edges. All other states denote fixed remaining suffixes of seed words.
    Only the empty-suffix state accepts; no suffix state returns to a control.
    """
    def __init__(self, forward, backward, seeds, deadline=None):
        self.deadline = deadline
        n = forward.system.size
        suffixes = sorted({u[i:] for _, u in seeds for i in range(len(u) + 1)})
        # An empty seed list denotes the empty language at every control.
        if () not in suffixes:
            suffixes.append(())
        suffix_id = {u: n + i for i, u in enumerate(suffixes)}
        size = n + len(suffixes)
        epsilon = [(backward.balanced[p] if p < n else 1 << p) for p in range(size)]
        transitions = [[0] * size for _ in (0, 1)]
        for p, a, q in backward.system.pop:
            transitions[a][p] |= 1 << q
        for u, q in suffix_id.items():
            if u:
                transitions[u[0]][q] |= 1 << suffix_id[u[1:]]
        for p, u in sorted(seeds):
            reached = forward.balanced[p]
            for i in range(len(u) + 1):
                check_time(deadline)
                for r in bits(reached):
                    epsilon[r] |= 1 << suffix_id[u[i:]]
                if i < len(u):
                    reached = forward.step(reached, u[i])
        transitive_closure(epsilon, deadline)
        self.epsilon, self.transitions = epsilon, transitions
        self.final = 1 << suffix_id[()]
        self.size = size
        self._step_cache = {}

    def step(self, states, letter):
        check_time(self.deadline)
        key = states, letter
        if key not in self._step_cache:
            targets = 0
            for p in bits(states):
                targets |= self.transitions[letter][p]
            closed = 0
            for q in bits(targets):
                closed |= self.epsilon[q]
            self._step_cache[key] = closed
        return self._step_cache[key]

    def accepts(self, q, word):
        states = self.epsilon[q]
        for a in word:
            states = self.step(states, a)
        return bool(states & self.final)

    def productive(self):
        """Exact nonempty-language controls; independent of prefix closure."""
        edges = [self.epsilon[p] | self.transitions[0][p] | self.transitions[1][p]
                 for p in range(self.size)]
        good = self.final
        while True:
            check_time(self.deadline)
            old = good
            for p, row in enumerate(edges):
                if row & good:
                    good |= 1 << p
            if old == good:
                return good

    def graph(self, variables):
        """Determinize accepting subsets; rejecting successors become bottom.

        Correct for the prefix-closed seed/forced-root closure constructed here.
        The caller must not use this conversion for arbitrary NFA languages.
        """
        nodes, ids, pending = [None], {}, deque()
        productive = self.productive()

        def intern(states):
            if not states & self.final:
                if states & productive:
                    raise ValueError('closure is not prefix-closed: a rejected residual can accept an extension')
                return 0
            if states not in ids:
                ids[states] = len(nodes)
                nodes.append(None)
                pending.append(states)
            return ids[states]

        roots = {name: intern(self.epsilon[q]) for q, name in enumerate(variables)}
        while pending:
            check_time(self.deadline)
            states = pending.popleft()
            nodes[ids[states]] = [intern(self.step(states, a)) for a in (0, 1)]
        return {'nodes': nodes, 'roots': roots}


def candidate_words(problem):
    """Finite syntax hints, then a fair length-first enumeration of all words."""
    hints = {()}

    def visit(e, path):
        if e[0] == 'prod':
            hints.add(path)
            visit(e[1], path + (0,))
            visit(e[2], path + (1,))

    for pair in (*problem.constraints, problem.query):
        for e in pair:
            visit(e, ())
    yield from sorted(hints, key=lambda w: (len(w), w))
    for length in count():
        for word in product((0, 1), repeat=length):
            if word not in hints:
                yield word


def extract(problem, deadline=None, max_words=None):
    """Return a graph on success; never infer entailment from failed search."""
    tried = 0
    try:
        system = normalize(problem, deadline)
        forward = PopMachine(system, deadline)
        backward = PopMachine(system.reverse(), deadline)
        for word in candidate_words(problem):
            check_time(deadline)
            if max_words is not None and tried >= max_words:
                return {'status': 'UNKNOWN', 'candidates': tried, 'reason': 'word_limit'}
            tried += 1
            seeds = {(q, ()) for q in system.forced}
            seeds.update((system.left, word[:i]) for i in range(len(word) + 1))
            nfa = ClosureNFA(forward, backward, seeds, deadline)
            productive = nfa.productive()
            if any(productive & (1 << q) for q in system.denied):
                continue
            if nfa.accepts(system.right, word):
                continue
            if not nfa.accepts(system.left, word):
                raise ValueError('canonical closure lost its separating-path seed')
            return {'status': 'FOUND', 'candidates': tried,
                    'separating_path': list(word), 'model': nfa.graph(problem.variables),
                    'normalized_controls': system.size, 'nfa_states': nfa.size,
                    'method': 'canonical finite-seed NFA and subset graph'}
    except TimeoutError:
        return {'status': 'UNKNOWN', 'candidates': tried, 'reason': 'time_limit'}
    except (RecursionError, MemoryError):
        return {'status': 'UNKNOWN', 'candidates': tried, 'reason': 'extraction_resource_limit'}


if __name__ == '__main__':
    # The CLI runs this worker under the same process-group time/memory limits
    # as Lean. The result file keeps large graphs out of compiler-output tails.
    import json
    from pathlib import Path
    import sys
    from subtail import parse_problem

    data = json.loads(Path(sys.argv[1]).read_text())
    result = extract(parse_problem(data), time.monotonic() + float(sys.argv[3]))
    Path(sys.argv[2]).write_text(json.dumps(result))
