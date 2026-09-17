#!/usr/bin/env python3
"""Independent semantic bridge audit, not a general subtype solver.

The new reference implementation uses a balanced-path grammar and minimum-stack
factorization. Optional --repository compares whole regular languages with the
repository's P-automaton implementation and checks the C029/C031 interfaces.
No finite word/stack cutoff is used to certify general non-entailment or NO.
Python 3.10+, standard library only. Run without -O.
"""
from __future__ import annotations
import argparse
from collections import Counter, deque
from dataclasses import dataclass
from itertools import product
import hashlib
import json
from math import lcm
from pathlib import Path
import random

BASE = '8ed4f45b563cda0ae3d31980fc14e6d61a35357a'
SEED = 20260917041
PINS = {
    'topfree_bridge.py': '0092b9c4ed8474d91db5cc5dbb72b1e7f5f7ad3f',
    'summary_bridge.py': 'f6a222891d9d7ca3b2995c82dbecf7182c64cb9f',
    'safe_extensions.py': '866b04fa67fa14684e56db75ce6cd850dff82009',
    'infinite_extensions.py': 'eda28ac44cbfe969a5aa83b2cade036b0f171fdc',
    'terminal_realization.py': '00b5dbb2ab345fd15db8660e8ae5179b0bfc2969',
    'border_lab.py': '1144ae52379e0417772e79582269cacd91c5bc17',
}


def bits(mask):
    while mask:
        b = mask & -mask
        yield b.bit_length() - 1
        mask -= b


class NFA:
    """Integer-labelled epsilon-NFA; inclusion is exhaustive subset BFS."""
    def __init__(self, n):
        self.eps = [0] * n
        self.edges = [[0, 0] for _ in range(n)]
        self.final = 0
        self._closures = None

    def node(self):
        n = len(self.eps)
        self.eps.append(0)
        self.edges.append([0, 0])
        self._closures = None
        return n

    def close(self, ss):
        if self._closures is None:
            e = [x | (1 << p) for p, x in enumerate(self.eps)]
            for k in range(len(e)):
                for p in range(len(e)):
                    if e[p] >> k & 1:
                        e[p] |= e[k]
            self._closures = e
        answer = 0
        for p in bits(ss):
            answer |= self._closures[p]
        return answer

    def step(self, ss, a):
        out = 0
        for p in bits(self.close(ss)):
            out |= self.edges[p][int(a)]
        return self.close(out)

    def after(self, p, w):
        ss = self.close(1 << p)
        for a in w:
            ss = self.step(ss, a)
        return ss

    def accepts(self, p, w):
        return bool(self.after(p, w) & self.final)

    def nonempty(self, ss):
        seen = self.close(ss)
        todo = list(bits(seen))
        for p in todo:
            if (1 << p) & self.final:
                return True
            nxt = self.close(self.edges[p][0] | self.edges[p][1]) & ~seen
            seen |= nxt
            todo.extend(bits(nxt))
        return False


def inclusion(A, sa, B, sb):
    first = (A.close(sa), B.close(sb))
    queue = deque([first])
    parents = {first: None}
    while queue:
        p, q = node = queue.popleft()
        if p & A.final and not q & B.final:
            w = ''
            while parents[node] is not None:
                node, a = parents[node]
                w = a + w
            return False, w, len(parents)
        for a in '01':
            nxt = A.step(p, a), B.step(q, a)
            if nxt not in parents:
                parents[nxt] = node, a
                queue.append(nxt)
    return True, None, len(parents)


def equivalent(A, p, B, q):
    x = inclusion(A, 1 << p, B, 1 << q)
    y = inclusion(B, 1 << q, A, 1 << p)
    assert x[0] and y[0], (x, y)
    return x[2] + y[2]


def prefix_closed(A, p):
    """A rejecting reachable subset must have no accepting continuation."""
    first = A.close(1 << p)
    seen = {first}
    todo = [first]
    for ss in todo:
        if not ss & A.final and A.nonempty(ss):
            return False
        for a in '01':
            nxt = A.step(ss, a)
            if nxt not in seen:
                seen.add(nxt)
                todo.append(nxt)
    return True


@dataclass(frozen=True)
class System:
    n: int
    constraints: tuple[tuple, ...]

    def rules(self):
        out = []
        for c in self.constraints:
            if c[0] == 'leq':
                out.append((c[1], 'e', '', c[2]))
            elif c[0] == 'lower':
                x, y, t = c[1:]
                out.extend(((x, '+', '0', t), (y, '+', '1', t)))
            elif c[0] == 'upper':
                s, x, y = c[1:]
                out.extend(((s, '-', '0', x), (s, '-', '1', y)))
            elif c[0] != 'denial':
                raise ValueError(c)
        return tuple(out)

    def forced(self):
        return {c[3] for c in self.constraints if c[0] == 'lower'}

    def denied(self):
        return {c[1] for c in self.constraints if c[0] == 'denial'}


def reverse(rules):
    return tuple((q, {'e': 'e', '+': '-', '-': '+'}[op], a, p)
                 for p, op, a, q in rules)


def grammar_summary(n, rules):
    """Balanced relation E ::= epsilon | eps-edge | EE | push E matching-pop.

    No seed automaton and no P-automaton edge saturation are used here.
    Letter edges consume original stack symbols between balanced segments.
    """
    E = [1 << p for p in range(n)]
    pops = {(p, a): set() for p in range(n) for a in '01'}
    pushes = []
    for p, op, a, q in rules:
        if op == 'e':
            E[p] |= 1 << q
        elif op == '-':
            pops[p, a].add(q)
        else:
            pushes.append((p, a, q))
    while True:
        before = tuple(E)
        for k in range(n):
            for p in range(n):
                if E[p] >> k & 1:
                    E[p] |= E[k]
        for p, a, q in pushes:
            for r in bits(E[q]):
                for t in pops[r, a]:
                    E[p] |= 1 << t
        if tuple(E) == before:
            break
    A = NFA(n)
    A.eps = E
    for (p, a), targets in pops.items():
        A.edges[p][int(a)] = sum(1 << q for q in targets)
    return A


def post_language(n, rules, seeds):
    """Post*(seeds) by the minimum-stack factorization, over ALL word lengths.

    (p,u)->*(q,v) iff u=xz, v=yz and, for some m,
    p --Pop_W(x)--> m and q --Pop_reverse(W)(y)--> m.
    Attach literal z suffixes only via fresh non-control nodes.
    """
    W = grammar_summary(n, rules)
    R = grammar_summary(n, reverse(rules))
    A = NFA(n)
    A.eps = R.eps[:]
    A.edges = [row[:] for row in R.edges]
    f = A.node()
    A.final = 1 << f
    for p, u in seeds:
        for cut in range(len(u) + 1):
            ends = W.after(p, u[:cut])
            z = u[cut:]
            entry = f
            for a in reversed(z):
                node = A.node()
                A.edges[node][int(a)] = 1 << entry
                entry = node
            for q in bits(ends):
                A.eps[q] |= 1 << entry
    return A


def forced_model(S):
    return post_language(S.n, S.rules(), [(p, '') for p in sorted(S.forced())])


def satisfiable(S):
    A = forced_model(S)
    return not any(A.nonempty(1 << p) for p in S.denied())


def model_errors(S, A):
    out = []
    for c in S.constraints:
        op = c[0]
        if op == 'denial':
            if A.nonempty(1 << c[1]):
                out.append(('denial', c[1]))
        elif op == 'leq':
            if not inclusion(A, 1 << c[1], A, 1 << c[2])[0]:
                out.append(c)
        elif op == 'upper':
            for a, t in zip('01', c[2:]):
                if not inclusion(A, A.step(1 << c[1], a), A, 1 << t)[0]:
                    out.append(c)
        else:
            x, y, t = c[1:]
            if not A.accepts(t, ''):
                out.append(('root', t))
            for a, p in zip('01', (x, y)):
                if not inclusion(A, 1 << p, A, A.step(1 << t, a))[0]:
                    out.append(c)
    if any(not prefix_closed(A, p) for p in range(S.n)):
        out.append(('not-prefix-closed',))
    return out


def canonical(S, alpha, beta, w):
    seeds = [(p, '') for p in sorted(S.forced())]
    seeds += [(alpha, w[:i]) for i in range(len(w) + 1)]
    A = post_language(S.n, S.rules(), seeds)
    return (not model_errors(S, A) and A.accepts(alpha, w)
            and not A.accepts(beta, w)), A


def cut_characterization(S, alpha, beta, w):
    if not satisfiable(S):
        return False
    W = grammar_summary(S.n, S.rules())
    R = grammar_summary(S.n, reverse(S.rules()))
    B = [W.after(alpha, w[:i]) for i in range(len(w) + 1)]
    A = [R.after(beta, w[:i]) for i in range(len(w) + 1)]
    if A[-1] & sum(1 << p for p in S.forced()):
        return False
    # Under satisfiability, every denied stack reachable from a prefix seed
    # has a prefix reaching the same denial with empty stack.
    if any(ss & sum(1 << p for p in S.denied()) for ss in B):
        return False
    for i in range(len(w) + 1):
        for j in range(i, len(w) + 1):
            if B[i] & A[j] and w[i:].startswith(w[j:]):
                return False
    return True


def all_words(bound):
    for length in range(bound + 1):
        for cs in product('01', repeat=length):
            yield ''.join(cs)


def random_system(rng, n, length):
    cs = []
    for _ in range(length):
        op = rng.choice(('leq', 'lower', 'upper', 'denial'))
        arity = {'leq': 2, 'lower': 3, 'upper': 3, 'denial': 1}[op]
        cs.append((op, *(rng.randrange(n) for _ in range(arity))))
    return System(n, tuple(cs))


def finite_pop_closure(n, rules, seeds):
    """Exact only when there are no pushes; this finite class is checked."""
    assert not any(op == '+' for p, op, a, q in rules)
    seen = set(seeds)
    todo = list(seeds)
    for p, w in todo:
        for s, op, a, q in rules:
            if s != p or (op == '-' and not w.startswith(a)):
                continue
            nxt = q, w if op == 'e' else w[1:]
            if nxt not in seen:
                seen.add(nxt)
                todo.append(nxt)
    return seen


def finite_nfa(n, configurations):
    A = NFA(n)
    f = A.node()
    A.final = 1 << f
    for p, word in sorted(configurations):
        at = p
        for a in word:
            t = A.node()
            A.edges[at][int(a)] |= 1 << t
            at = t
        A.eps[at] |= 1 << f
    return A


def fixtures(counts):
    # x includes (x x bottom), so its least model is the infinite left spine.
    S = System(2, (('lower', 0, 1, 0), ('denial', 1)))
    ok, A = canonical(S, 0, 1, '')
    assert ok and satisfiable(S) and not model_errors(S, A)
    expected = NFA(2)
    expected.final = 1
    expected.edges[0][0] = 1
    equivalent(A, 0, expected, 0)
    assert not A.nonempty(1 << 1)
    counts['exact_infinite_spine_models'] += 1
    # Omitting proper prefixes silently loses forced beta membership.
    T = System(3, (('lower', 0, 2, 1), ('denial', 2)))
    whole = post_language(3, T.rules(), [(0, '0'), (1, '')])
    full = post_language(3, T.rules(), [(0, ''), (0, '0'), (1, '')])
    assert not whole.accepts(1, '0') and full.accepts(1, '0')
    assert not prefix_closed(whole, 0)
    assert not canonical(T, 0, 1, '0')[0]
    counts['missing_prefix_regressions'] += 1
    # A denial at a nonempty stack is reached by a push target forced at root.
    U = System(2, (('lower', 0, 0, 1), ('denial', 1)))
    assert not satisfiable(U)
    counts['forced_root_unsat_regressions'] += 1
    # Empty word, diagonal and final-column obligations are not optional.
    V = System(2, ())
    assert canonical(V, 0, 1, '')[0]
    assert not canonical(V, 0, 0, '')[0]
    assert cut_characterization(V, 0, 1, '')
    assert not cut_characterization(V, 0, 0, '')
    counts['empty_query_regressions'] += 2
    return {'infinite_spine': {'constraints': S.constraints,
                             'x_language': '0*', 'bottom_language': 'empty',
                             'separating_path': '',
                             'finite_tree_satisfiability': False,
                             'arbitrary_tree_satisfiability': True}}


def local_suite():
    rng = random.Random(SEED)
    counts = Counter()
    named = fixtures(counts)
    for _ in range(100):
        n = rng.randrange(1, 5)
        rules = tuple((rng.randrange(n), rng.choice(('e', '-')), rng.choice('01'), rng.randrange(n))
                      for _ in range(rng.randrange(1, 10)))
        seeds = [(rng.randrange(n), rng.choice(list(all_words(4)))) for _ in range(3)]
        exact = finite_pop_closure(n, rules, seeds)
        A = post_language(n, rules, seeds)
        B = finite_nfa(n, exact)
        for p in range(n):
            counts['no_push_inclusion_states'] += equivalent(A, p, B, p)
            counts['complete_no_push_languages'] += 1
    # These comparisons use exact reachability/model checks per supplied word,
    # but the sample of systems and candidate paths is explicitly finite.
    for _ in range(80):
        S = random_system(rng, rng.randrange(2, 5), rng.randrange(1, 9))
        F = forced_model(S)
        assert all(prefix_closed(F, p) for p in range(S.n))
        counts['forced_models_prefix_closed'] += 1
        if satisfiable(S):
            assert not model_errors(S, F)
            counts['satisfiable_random_systems'] += 1
        else:
            counts['unsatisfiable_random_systems'] += 1
        for w in all_words(3):
            ok, A = canonical(S, 0, 1, w)
            assert ok == cut_characterization(S, 0, 1, w), (S, w)
            counts['canonical_vs_cut_pairs'] += 1
            if ok:
                assert not model_errors(S, A)
                counts['all_depth_countermodels_checked'] += 1
    return {'counts': dict(sorted(counts.items())), 'fixtures': named}


def convert_system(S, module):
    constructors = {'lower': module.ProductLower, 'upper': module.ProductUpper,
                    'leq': module.VariableLeq, 'denial': module.BottomDenial}
    # Isolated variables remain part of the declared comparison signature.
    cs = [constructors[c[0]](*c[1:]) for c in S.constraints]
    cs.extend(module.VariableLeq(p, p) for p in range(S.n))
    return module.NormalizedSystem(cs)


def convert_nfa(original, controls, final=None):
    ids = {p: p for p in range(controls)}
    for p in original.states:
        if p not in ids:
            ids[p] = len(ids)
    A = NFA(len(ids))
    for p, targets in original.eps.items():
        A.eps[ids[p]] = sum(1 << ids[q] for q in targets)
    for p, row in original.edges.items():
        for a, targets in row.items():
            A.edges[ids[p]][int(a)] = sum(1 << ids[q] for q in targets)
    A.final = sum(1 << ids[p] for p in (original.final if final is None else final))
    return A


def repository_suite():
    # An explicit opt-in is needed because this imports the repository code.
    import topfree_bridge as old
    import summary_bridge as summary
    import terminal_realization as realization
    from border_lab import Instance, witness, border_witness
    from safe_extensions import (absorption_holds, safe_states, zero_region,
                                 active_rays, primitive)
    from infinite_extensions import (infinite_extension_decision, monitor_start,
                                     monitor_step)
    root = Path(old.__file__).resolve().parent
    actual = {}
    for name, expected in PINS.items():
        data = (root / name).read_bytes()
        actual[name] = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
        if actual[name] != expected:
            raise RuntimeError('Reviewed dependency changed: ' + name)
    counts = Counter()
    rng = random.Random(SEED + 1)
    words4 = list(all_words(4))
    for _ in range(72):
        S = random_system(rng, rng.randrange(2, 5), rng.randrange(1, 10))
        original = convert_system(S, old)
        rules = S.rules()
        for rr in (rules, reverse(rules)):
            grammar = grammar_summary(S.n, rr)
            ops = {'e': 'eps', '+': 'push', '-': 'pop'}
            legacy = summary.build_pop_summary(
                [old.PDSRule(p, q, ops[op], None if op == 'e' else a) for p, op, a, q in rr],
                range(S.n))
            for q in range(S.n):
                grammar.final = 1 << q
                C = convert_nfa(legacy, S.n, {q})
                for p in range(S.n):
                    counts['whole_pop_language_product_states'] += equivalent(grammar, p, C, p)
                    counts['whole_pop_language_equivalences'] += 1
        seeds = [(rng.randrange(S.n), rng.choice(words4)) for _ in range(3)]
        A = post_language(S.n, rules, seeds)
        legacy = old.ReachablePathSets(original, seeds)
        C = convert_nfa(legacy.automaton, S.n)
        for p in range(S.n):
            counts['whole_post_language_product_states'] += equivalent(A, p, C, p)
            counts['whole_post_language_equivalences'] += 1
        assert satisfiable(S) == old.is_satisfiable(original)
        counts['sat_guard_comparisons'] += 1
        if not satisfiable(S):
            try:
                summary.build_summary_bridge(original, 0, 1)
            except ValueError:
                counts['unsat_summary_guards'] += 1
            else:
                raise AssertionError('Missing satisfiability guard')
            continue
        bridge = summary.build_summary_bridge(original, 0, 1)
        assert absorption_holds(bridge.instance)
        counts['actual_summary_absorption_checks'] += 1
        for w in all_words(3):
            ok, A = canonical(S, 0, 1, w)
            assert ok == witness(bridge.instance, w) == border_witness(bridge.instance, w)
            counts['actual_summary_word_comparisons'] += 1
        result = old.canonical_countermodel(original, 0, 1, rng.choice(words4))
        if result.model is not None:
            C = convert_nfa(result.model.automaton, S.n)
            assert all(prefix_closed(C, p) for p in range(S.n))
            if result.status == 'YES':
                assert not model_errors(S, C)
                counts['legacy_infinite_model_certificates'] += 1
    # C030: exact same-word subtype interpretation, with all boundary flags.
    for _ in range(80):
        k = rng.randrange(1, 5)
        finals = frozenset(q for q in range(k) if rng.random() < .4) or frozenset({k-1})
        delta = tuple((-1, -1) if q in finals else tuple(rng.randrange(-1, k) for _ in '01')
                      for q in range(k))
        G = frozenset((p, q) for p in range(k) for q in range(k) if rng.random() < .18)
        bad = frozenset(q for q in range(k) if rng.random() < .12)
        I = Instance(delta, finals, G, bad, rng.randrange(k))
        R = realization.realize(I)
        S = System(R.variables, R.constraints)
        assert satisfiable(S)
        counts['terminal_realizations_satisfiable'] += 1
        for w in all_words(4):
            assert witness(I, w) == cut_characterization(S, R.alpha, R.beta, w), (I, w)
            counts['terminal_realization_paths'] += 1
    # Monitor invariant for primitive rays: compare to literal cut pairs.
    for _ in range(64):
        k = rng.randrange(2, 5)
        F = frozenset({k-1})
        G = frozenset((p, q) for p in range(k) for q in range(k-1) if rng.random() < .2)
        delta = tuple(tuple(rng.randrange(k) for _ in '01') if q != k-1 else (k-1, k-1)
                      for q in range(k))
        I = Instance(delta, F, G)
        for period in ('0', '1', '01', '001', '011'):
            d = len(period)
            for w in all_words(6):
                offset = len(w) % d
                node = monitor_start(I, d) if I.start in safe_states(I) else None
                for a in w:
                    node = monitor_step(I, period, offset, node, a) if node is not None else None
                run = I.run(w)
                if run is None or any(q not in safe_states(I) for q in run):
                    assert node is None
                    continue
                conflict = False
                for i in range(len(w)+1):
                    for j in range(i+1, len(w)+1):
                        if ((run[i],run[j]) in G and (j-i)%d == 0 and
                            all(a == period[(t-len(w))%d] for t,a in enumerate(w[i:], i))):
                            conflict = True
                assert node[-1] == conflict, (I, period, w)
                counts['period_monitor_literal_checks'] += 1
                if run[-1] in zero_region(I):
                    assert conflict == (period in active_rays(I, w))
                    counts['active_ray_phase_checks'] += 1
    # All-length independent oracle for unique labelled infinite trajectories.
    for _ in range(320):
        k = rng.randrange(1, 6)
        F = frozenset(q for q in range(k) if rng.random() < .5)
        G = frozenset((p,q) for p in range(k) for q in range(k) if rng.random() < .13)
        zero = F - {q for p,q in G}
        rows = []
        for p in range(k):
            targets = sorted(zero) if p in F else list(range(k))
            row = [-1,-1]
            if targets and rng.random() < .9:
                row[rng.randrange(2)] = rng.choice(targets)
            rows.append(tuple(row))
        I = Instance(tuple(rows), F, G, frozenset(q for q in range(k) if rng.random()<.05))
        safe = safe_states(I)
        states = [I.start]
        labels = ''
        seen = {}
        q = I.start
        while q in safe and q not in seen:
            seen[q] = len(labels)
            edges = [(a,t) for a,t in zip('01',I.delta[q]) if t in safe]
            if not edges:
                break
            a,q = edges[0]
            labels += a
            states.append(q)
        expect = False
        if q in seen and states[-1] == q and len(labels) > seen[q]:
            cycle_at = seen[q]
            stem, cycle = labels[:cycle_at], labels[cycle_at:]
            zcut = next((i for i,t in enumerate(states) if t in zero_region(I)), None)
            if zcut is not None:
                def letter(t):
                    return stem[t] if t < len(stem) else cycle[(t-len(stem))%len(cycle)]
                prefix = ''.join(letter(i) for i in range(zcut))
                trace = I.run(prefix)
                blocked = False
                for i in range(zcut+1):
                    for j in range(i+1,zcut+1):
                        if (trace[i],trace[j]) not in G:
                            continue
                        # Two tails are ultimately periodic with the SAME cycle
                        # length. A complete common period after both stems suffices.
                        limit = max(0, len(stem)-i, len(stem)-j) + len(cycle)
                        if all(letter(i+t)==letter(j+t) for t in range(limit)):
                            blocked = True
                expect = not blocked
        answer = infinite_extension_decision(I, max_states=200000)
        assert answer['status'] in ('YES','NO_INFINITE_EXTENSION'), answer
        assert (answer['status']=='YES') == expect, (I,answer,expect)
        if expect:
            assert witness(I,answer['word'])
        counts['complete_unique_trajectory_oracles'] += 1
    # C031: independent safe-sink extension of every sampled finite-only witness.
    for _ in range(100):
        k = rng.randrange(2,5)
        F = frozenset(q for q in range(k) if rng.random()<.5)
        G = frozenset((p,q) for p in range(k) for q in range(k) if rng.random()<.12)
        zero = F-{q for p,q in G}
        rows = tuple(tuple(rng.choice([-1]+sorted(zero)) if p in F else rng.randrange(-1,k)
                           for _ in '01') for p in range(k))
        I = Instance(rows,F,G,frozenset(q for q in range(k) if rng.random()<.1))
        J = realization.terminal_restriction(I)
        assert all(J.delta[f]==(-1,-1) for f in J.final)
        safe = safe_states(I)
        for w in all_words(5):
            if witness(J,w):
                assert witness(I,w)
                counts['terminal_inclusion_witnesses'] += 1
            if not witness(I,w):
                continue
            # Exhaust all reachable simple paths. A detected cycle means this
            # is an infinite-continuation case, not a failed terminal proof.
            q=I.run(w)[-1]
            todo=[(q,'',(q,))]
            cycle=False
            sinks=[]
            for p,u,history in todo:
                successors=[(a,t) for a,t in zip('01',I.delta[p]) if t in safe]
                if not successors:
                    sinks.append(u)
                for a,t in successors:
                    if t in history:
                        cycle=True
                    else:
                        todo.append((t,u+a,history+(t,)))
            if not cycle:
                assert sinks
                u=min(sinks,key=lambda x:(len(x),x))
                assert len(u)<=k-1 and witness(I,w+u) and witness(J,w+u)
                counts['finite_only_sink_extensions'] += 1
    return {'counts': dict(sorted(counts.items())), 'verified_git_blobs': actual}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repository', action='store_true')
    ap.add_argument('--output', type=Path)
    args=ap.parse_args()
    if not __debug__:
        ap.error('Assertions are required; do not use -O')
    report={'status':'PASS', 'base_commit':BASE, 'seed':SEED,
            'local':local_suite(),
            'limits':['Finite corpora do not prove the all-input rank closure theorem.',
                      'Whole-language equivalence checks exhaust finite NFA subset products.',
                      'Unique-trajectory oracles decide all lengths for their stated class.',
                      'No Lean verification or external mathematical referee is claimed.']}
    if args.repository:
        report['repository']=repository_suite()
    text=json.dumps(report,indent=2,sort_keys=True)+'\n'
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(text,encoding='utf-8')
    print(text)


if __name__=='__main__':
    main()
