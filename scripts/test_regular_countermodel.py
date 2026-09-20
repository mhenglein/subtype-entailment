"""Independent finite closures and original-input graph checks for extraction."""
from collections import deque
from itertools import product
import random
import time
import unittest

import regular_countermodel as rc
import subtail


def word_set(depth):
    return [w for d in range(depth + 1) for w in product((0, 1), repeat=d)]


def literal_closure(system, seeds):
    """Only called on acyclic control graphs: all runs have < size steps.

    This is literal stack rewriting, with neither summaries nor suffix splits.
    Acyclicity makes the *whole* reachable set finite; there is no depth cutoff.
    """
    assert all(p < q for p, q in system.epsilon)
    assert all(p < q for p, _, q in system.push | system.pop)
    reached, queue = set(seeds), deque(seeds)
    while queue:
        p, word = queue.popleft()
        candidates = [(q, word) for s, q in system.epsilon if s == p]
        candidates += [(q, (a,) + word) for s, a, q in system.push if s == p]
        candidates += [(q, word[1:]) for s, a, q in system.pop
                       if s == p and word and word[0] == a]
        for c in candidates:
            if c not in reached:
                reached.add(c)
                queue.append(c)
    return reached


class ExtractionTests(unittest.TestCase):
    def test_suffix_is_appended_on_right(self):
        system = rc.System(2, set(), {(0, 1, 1)}, set(), set(), set(), 0, 1)
        nfa = rc.ClosureNFA(rc.PopMachine(system), rc.PopMachine(system.reverse()), {(0, (0, 1))})
        self.assertTrue(nfa.accepts(1, (1, 0, 1)))
        self.assertFalse(nfa.accepts(1, (0, 1, 1)))

    def test_graph_rejects_non_prefix_closed_language(self):
        system = rc.System(1, set(), set(), set(), set(), set(), 0, 0)
        nfa = rc.ClosureNFA(rc.PopMachine(system), rc.PopMachine(system.reverse()), {(0, (0,))})
        with self.assertRaisesRegex(ValueError, 'not prefix-closed'):
            nfa.graph(('x',))

    def test_nfa_matches_complete_literal_acyclic_closures(self):
        rng = random.Random(5701)
        for sample in range(80):
            n = rng.randrange(1, 6)
            eps, push, pop = set(), set(), set()
            for p in range(n):
                for q in range(p + 1, n):
                    if rng.random() < .3:
                        eps.add((p, q))
                    for a in (0, 1):
                        if rng.random() < .25:
                            push.add((p, a, q))
                        if rng.random() < .25:
                            pop.add((p, a, q))
            system = rc.System(n, eps, push, pop, set(), set(), 0, 0)
            seeds = {(rng.randrange(n), rng.choice(word_set(3))) for _ in range(3)}
            reached = literal_closure(system, seeds)
            forward, backward = rc.PopMachine(system), rc.PopMachine(system.reverse())
            nfa = rc.ClosureNFA(forward, backward, seeds)
            # Complete relevant domain: max input height plus < n transitions.
            bound = max(len(w) for _, w in seeds) + n - 1
            for q in range(n):
                for w in word_set(bound):
                    self.assertEqual(nfa.accepts(q, w), (q, w) in reached, (sample, q, w))
                self.assertEqual(bool(nfa.productive() & (1 << q)),
                                 any(p == q for p, _ in reached), (sample, q))

    def test_cyclic_nfa_against_independent_predecessor_saturation(self):
        from experiments import check_stack_summary as oracle
        rng = random.Random(5704)
        for sample in range(60):
            n = rng.randrange(1, 4)
            epsilon = {(p,q) for p in range(n) for q in range(n) if rng.random() < .2}
            push = {(p,a,q) for p in range(n) for a in (0,1) for q in range(n) if rng.random() < .2}
            pop = {(p,a,q) for p in range(n) for a in (0,1) for q in range(n) if rng.random() < .2}
            system = rc.System(n, epsilon, push, pop, set(), set(), 0, 0)
            source = oracle.System(n, frozenset(epsilon),
                frozenset((a,p,q) for p,a,q in push), frozenset((a,p,q) for p,a,q in pop))
            seeds = {(rng.randrange(n), rng.choice(word_set(3))) for _ in range(3)}
            nfa = rc.ClosureNFA(rc.PopMachine(system), rc.PopMachine(system.reverse()), seeds)
            for q in range(n):
                for word in word_set(3):
                    pre = oracle.predecessor(source, q, word)
                    self.assertEqual(nfa.accepts(q, word), any(pre(p,u) for p,u in seeds),
                                     (sample, q, word))
                pre = oracle.predecessor(source, q, None)
                self.assertEqual(bool(nfa.productive() & (1 << q)),
                                 any(pre(p,u) for p,u in seeds), (sample,q))

    def check(self, data):
        p = subtail.parse_problem(data)
        result = rc.extract(p, time.monotonic() + 5, max_words=128)
        self.assertEqual(result['status'], 'FOUND', result)
        checked = subtail.check_countermodel(p, result['model'])
        self.assertTrue(checked['valid'], (data, result, checked))
        return result, checked

    def test_alternating_infinite_spines_beyond_old_library(self):
        xp, yp = {'prod': ['bottom', 'y']}, {'prod': ['x', 'bottom']}
        data = {'variables': ['x', 'y'],
                'constraints': [['x', xp], [xp, 'x'], ['y', yp], [yp, 'y']],
                'query': ['x', {'prod': ['bottom', 'bottom']}]}
        result, checked = self.check(data)
        self.assertEqual(checked['separating_path'], [1])
        p = subtail.parse_problem(data)
        old_nodes = [None, [0, 0], [2, 2], [3, 0], [0, 4]]
        for roots in product(range(5), repeat=2):
            self.assertFalse(subtail.check_countermodel(p, {'nodes': old_nodes,
                'roots': dict(zip(p.variables, roots))})['valid'])

    def test_no_variables_and_nested_expression_separator(self):
        _, checked = self.check({'variables': [], 'constraints': [],
            'query': [{'prod': ['bottom', {'prod': ['bottom', 'bottom']}]},
                      {'prod': ['bottom', 'bottom']}]})
        self.assertEqual(checked['separating_path'], [1])

    def test_all_finite_depth_three_valuations(self):
        def trees(d):
            if d == 0:
                return [None]
            smaller = trees(d - 1)
            return [None] + list(product(smaller, repeat=2))
        def expr(t):
            return 'bottom' if t is None else {'prod': [expr(t[0]), expr(t[1])]}
        def paths(t):
            if t is None:
                return set()
            return {()} | {(a,) + w for a in (0, 1) for w in paths(t[a])}
        for x, y in product(trees(3), repeat=2):
            if not paths(x) - paths(y):
                continue
            self.check({'variables': ['x', 'y'],
                'constraints': [['x', expr(x)], [expr(x), 'x'], ['y', expr(y)], [expr(y), 'y']],
                'query': ['x', 'y']})

    def test_denial_and_contradiction_remain_unknown(self):
        for data in [
            {'variables':['x'], 'constraints':[['x','bottom']], 'query':['x','bottom']},
            {'variables':['x'], 'constraints':[['x','bottom'],
                [{'prod':['x','bottom']},'x']], 'query':['x','bottom']},
            {'variables':['x'], 'constraints':[], 'query':['x','x']},
        ]:
            result = rc.extract(subtail.parse_problem(data), max_words=16)
            self.assertEqual(result['status'], 'UNKNOWN')
            self.assertEqual(result['reason'], 'word_limit')
        p = subtail.parse_problem({'variables':['x'], 'constraints':[], 'query':['x','bottom']})
        self.assertEqual(rc.extract(p, deadline=0)['reason'], 'time_limit')

    def test_generated_inputs_with_independent_cyclic_countermodels(self):
        rng = random.Random(5702)
        for sample in range(120):
            # This graph supplies an independent witness of non-entailment.
            # Premises are retained only when exact pair-graph inclusion holds.
            nodes = [None] + [[rng.randrange(5), rng.randrange(5)] for _ in range(4)]
            roots = {'x': rng.randrange(5), 'y': rng.randrange(5)}
            model = {'nodes': nodes, 'roots': roots}
            terms = ['bottom', 'x', 'y', {'prod':['x','y']},
                     {'prod':['bottom','x']}, {'prod':['y','bottom']}]
            valid, negative = [], []
            for s, t in product(terms, repeat=2):
                p = subtail.parse_problem({'variables':['x','y'], 'constraints':[], 'query':[s,t]})
                checked = subtail.check_countermodel(p, model)
                if not checked['valid']:
                    valid.append([s,t])
                elif len(checked['separating_path']) <= 3:
                    negative.append([s,t])
            if not negative:
                continue
            self.check({'variables':['x','y'],
                        'constraints':rng.sample(valid, min(5, len(valid))),
                        'query':rng.choice(negative)})


if __name__ == '__main__':
    unittest.main()
