"""Exact boundedness of realizable last-aligned-flag suffix lengths.

See notes/2026-09-07-realizable-lastflag-spectrum.md for the written argument.
An unbounded comparison spectrum is not a NO answer or a proof that no finite
necessary bound detects every bad word. Standard library; Python 3.9+.
"""
from collections import deque
from dataclasses import dataclass

from border_lab import Instance, Sandwich, border_witness, witness


class ResourceLimit(Exception):
    """An unfinished finite computation, never a negative answer."""


def _check_limit(value, name):
    if value is not None and (isinstance(value, bool) or not isinstance(value, int)
                              or value < 1):
        raise ValueError(name + ' must be a positive integer or None')


def _validate(I):
    k = len(I.delta)
    if k < 1 or not 0 <= I.start < k:
        raise ValueError('nonempty state set and valid start required')
    if not I.alphabet or len(set(I.alphabet)) != len(I.alphabet):
        raise ValueError('alphabet must have distinct letters')
    if any(len(row) != len(I.alphabet) or
           any(not isinstance(q, int) or q < -1 or q >= k for q in row)
           for row in I.delta):
        raise ValueError('invalid partial transition table')
    if any(not 0 <= q < k for q in I.final | I.bad):
        raise ValueError('invalid final or Bad state')
    if any(not (0 <= p < k and 0 <= q < k) for p, q in I.flags):
        raise ValueError('invalid flag')
    return all(all(q == -1 for q in I.delta[f]) for f in I.final)


def _reach(edges, initial):
    seen, todo = set(initial), deque(initial)
    while todo:
        for q in edges[todo.popleft()]:
            if q >= 0 and q not in seen:
                seen.add(q)
                todo.append(q)
    return seen


def boundary_slice(I, f):
    """Exact boundary-safe, productive f-slice; returns local-to-input map."""
    forbidden = set(I.bad) | {p for p, q in I.flags if p == q or q == f}
    if I.start in forbidden or f in forbidden:
        return None
    edges = [tuple(q for q in row if q >= 0 and q not in forbidden)
             if p not in forbidden else () for p, row in enumerate(I.delta)]
    back = [[] for _ in I.delta]
    for p, row in enumerate(edges):
        for q in row:
            back[q].append(p)
    live = sorted(_reach(edges, [I.start]) & _reach(back, [f]))
    if I.start not in live:
        return None
    index = {q: p for p, q in enumerate(live)}
    J = Instance(tuple(tuple(index.get(q, -1) for q in I.delta[p]) for p in live),
                 frozenset({index[f]}),
                 frozenset((index[p], index[q]) for p, q in I.flags
                           if p in index and q in index),
                 start=index[I.start], alphabet=I.alphabet)
    return J, live


def _heads(I):
    heads, todo = {I.start: ''}, deque([I.start])
    while todo:
        p = todo.popleft()
        for a, q in zip(I.alphabet, I.delta[p]):
            if q >= 0 and q not in heads:
                heads[q] = heads[p] + a
                todo.append(q)
    return heads


def _combined_machine(I):
    """Single states plus pairs; a positive-time flag kills a pair run."""
    k = len(I.delta)
    f = next(iter(I.final))
    pairs = [(p, q) for p in range(k) for q in range(k) if p != q and p != f]
    ix = {pair: k + j for j, pair in enumerate(pairs)}
    sink = k + len(pairs)
    generators = []
    for a in range(len(I.alphabet)):
        g = [q if q >= 0 else sink for q in (row[a] for row in I.delta)]
        for p, q in pairs:
            dest = (I.delta[p][a], I.delta[q][a])
            g.append(ix.get(dest, sink) if dest not in I.flags else sink)
        g.append(sink)
        generators.append(tuple(g))
    return generators, ix, {i: pair for pair, i in ix.items()}, sink


@dataclass
class ActionMonoid:
    actions: list
    edges: list
    representatives: list
    positive: list
    maximum: list
    longest: list
    incoming: list
    alphabet: str

    @classmethod
    def build(cls, generators, alphabet, max_monoid):
        identity = tuple(range(len(generators[0])))
        actions, ids, reps, positive, edges = [identity], {identity: 0}, [''], [None], []
        cursor = 0
        while cursor < len(actions):
            row = []
            for a, g in zip(alphabet, generators):
                effect = tuple(g[q] for q in actions[cursor])
                t = ids.get(effect)
                word = reps[cursor] + a
                if t is None:
                    if max_monoid is not None and len(actions) >= max_monoid:
                        raise ResourceLimit('transition-monoid cap')
                    t = len(actions)
                    ids[effect] = t
                    actions.append(effect)
                    reps.append(word)
                    positive.append(word)
                elif positive[t] is None:
                    positive[t] = word
                row.append(t)
            edges.append(row)
            cursor += 1
        incoming = [[] for _ in actions]
        indegree = [0] * len(actions)
        for p, row in enumerate(edges):
            for a, q in zip(alphabet, row):
                incoming[q].append((p, a))
                indegree[q] += 1
        # All vertices are reachable from the identity. Kahn survivors are
        # exactly vertices with a cyclic ancestor, hence infinite word classes.
        todo = deque(p for p, d in enumerate(indegree) if d == 0)
        maximum, longest, finite = [-1] * len(actions), [None] * len(actions), set()
        maximum[0], longest[0] = 0, ''
        while todo:
            p = todo.popleft()
            finite.add(p)
            for a, q in zip(alphabet, edges[p]):
                if maximum[p] + 1 > maximum[q]:
                    maximum[q], longest[q] = maximum[p] + 1, longest[p] + a
                indegree[q] -= 1
                if indegree[q] == 0:
                    todo.append(q)
        for p in range(len(actions)):
            if p not in finite:
                maximum[p], longest[p] = None, None
        return cls(actions, edges, reps, positive, maximum, longest, incoming, alphabet)

    def action_index(self, word):
        q = 0
        for a in word:
            q = self.edges[q][self.alphabet.index(a)]
        return q

    def lasso(self, target):
        """prefix loop^m suffix has the target action for every m>=0."""
        if self.maximum[target] is not None:
            raise ValueError('the requested action class is finite')
        chain, at, labels, q = [], {}, [], target
        while q not in at:
            at[q] = len(chain)
            chain.append(q)
            p, a = next((p, a) for p, a in self.incoming[q] if self.maximum[p] is None)
            labels.append(a)
            q = p
        i = at[q]
        result = {'prefix': self.representatives[q],
                  'loop': ''.join(reversed(labels[i:])),
                  'suffix': ''.join(reversed(labels[:i]))}
        assert result['loop']
        return result


def realize_template(template, m=1):
    """Reconstruct a bad accepted word; m>=1 for a pumping certificate."""
    if not isinstance(m, int) or m < 1:
        raise ValueError('pump exponent must be a positive integer')
    u, v = template['u'], template['v']
    if 'pump' in template:
        pump = template['pump']
        value = pump['prefix'] + pump['loop'] * m + pump['suffix']
        if pump['factor'] == 'u':
            u = value
        else:
            v = value
    x, e = template['head'], template['exponent']
    return {'word': x + (u + v) * e + u, 'i': len(x), 'j': len(x) + len(u) + len(v)}


def is_lastflag(I, word, i, j):
    """Direct certificate verifier, independent of the action abstraction."""
    c = I.run(word)
    n = len(word)
    if c is None or not I.admissible(word) or not (0 <= i < j < n):
        return False
    f = c[-1]
    if any((p, p) in I.flags or (p, f) in I.flags for p in c):
        return False
    return ((c[i], c[j]) in I.flags and word[i:].startswith(word[j:])
            and all((c[i+t], c[j+t]) not in I.flags for t in range(1, n-j+1)))


def _terms(I, monoid, pair_ix, pair_of, sink, max_checks, counts):
    """Enumerate exact (source, u-action, v-action, exponent) templates."""
    f, k = next(iter(I.final)), len(I.delta)
    sources = sorted({p for p, q in I.flags if p != q and p != f and q != f})
    for ai, A in enumerate(monoid.actions):
        for bi, B in enumerate(monoid.actions):
            if monoid.positive[bi] is None:
                continue
            for p in sources:
                counts['checks'] += 1
                if max_checks is not None and counts['checks'] > max_checks:
                    raise ResourceLimit('action-combination cap')
                q = B[A[p]]
                if (p, q) not in I.flags or (p, q) not in pair_ix:
                    continue
                r = pair_ix[p, q]
                for e in range(1, k):
                    end = A[r]
                    if end in pair_of and pair_of[end][1] == f:
                        counts['templates'] += 1
                        yield p, ai, bi, e
                    r = B[A[r]]
                    if r == sink:
                        break


def _analyze_slice(I, max_monoid, max_checks):
    f = next(iter(I.final))
    roots = [(p, q) for p, q in I.flags if p != q and p != f and q != f]
    if not roots:
        return {'status': 'FINITE', 'H': 0, 'monoid_states': 0, 'checks': 0,
                'templates': 0, 'maximum_certificate': None}
    generators, pair_ix, pair_of, sink = _combined_machine(I)
    monoid = ActionMonoid.build(generators, I.alphabet, max_monoid)
    heads = _heads(I)
    counts, H, certificate = {'checks': 0, 'templates': 0}, 0, None
    for p, ai, bi, e in _terms(I, monoid, pair_ix, pair_of, sink, max_checks, counts):
        template = {'head': heads[p], 'u': monoid.representatives[ai],
                    'v': monoid.positive[bi], 'exponent': e}
        ma, mb = monoid.maximum[ai], monoid.maximum[bi]
        if ma is None or (e > 1 and mb is None):
            factor, index = ('u', ai) if ma is None else ('v', bi)
            template['pump'] = dict(monoid.lasso(index), factor=factor)
            sample = realize_template(template)
            assert is_lastflag(I, **sample)
            return {'status': 'UNBOUNDED', 'monoid_states': len(monoid.actions),
                    **counts, 'pumping_certificate': template}
        length = e * ma + (e - 1) * (mb if e > 1 else 0)
        if length > H:
            H = length
            template['u'] = monoid.longest[ai]
            if e > 1:
                template['v'] = monoid.longest[bi]
            sample = realize_template(template)
            assert is_lastflag(I, **sample) and len(sample['word'])-sample['j'] == H
            certificate = template
    return {'status': 'FINITE', 'H': H, 'monoid_states': len(monoid.actions),
            **counts, 'maximum_certificate': certificate}


def spectrum(I, max_monoid=20000, max_checks=2000000):
    """Exact union of boundary slices; UNBOUNDED refers only to comparisons.

    None removes a resource cap; the uncapped analysis always terminates.
    FINITE includes the empty spectrum, with convention H=0.
    """
    _check_limit(max_monoid, 'max_monoid')
    _check_limit(max_checks, 'max_checks')
    if not _validate(I):
        return {'status': 'UNSUPPORTED', 'reason': 'accepting states must be terminal'}
    results, H, unknown, unbounded = [], 0, False, False
    for f in sorted(I.final):
        normalized = boundary_slice(I, f)
        if normalized is None:
            results.append({'final': f, 'status': 'FINITE', 'H': 0, 'empty_slice': True})
            continue
        J, mapping = normalized
        try:
            record = _analyze_slice(J, max_monoid, max_checks)
        except ResourceLimit as error:
            record = {'status': 'UNKNOWN', 'reason': str(error)}
        record.update(final=f, local_to_input=mapping)
        results.append(record)
        if record['status'] == 'UNBOUNDED':
            unbounded = True
        elif record['status'] == 'UNKNOWN':
            unknown = True
        else:
            H = max(H, record['H'])
    result = {'status': 'UNBOUNDED' if unbounded else 'UNKNOWN' if unknown else 'FINITE',
              'slices': results}
    if result['status'] == 'FINITE':
        result['H'] = H
    return result


def decide(I, max_monoid=20000, max_checks=2000000, max_search_states=200000):
    """Sound partial witness decider: finite spectra give exact decisions."""
    _check_limit(max_search_states, 'max_search_states')
    analysis = spectrum(I, max_monoid, max_checks)
    if analysis['status'] == 'UNSUPPORTED':
        return {'status': 'UNKNOWN', 'reason': analysis['reason'], 'analysis': analysis}
    unresolved, searches = False, []
    for record in analysis['slices']:
        if record.get('empty_slice'):
            continue
        if record['status'] != 'FINITE':
            unresolved = True
            continue
        J, _ = boundary_slice(I, record['final'])
        cap = max_search_states if max_search_states is not None else float('inf')
        answer = Sandwich(J, record['H'], 0).search(cap)
        searches.append(dict(answer, final=record['final']))
        if answer['status'] == 'YES':
            assert witness(I, answer['word']) and border_witness(I, answer['word'])
            return {'status': 'YES', 'word': answer['word'], 'analysis': analysis,
                    'searches': searches}
        unresolved |= answer['status'] == 'UNKNOWN'
    return {'status': 'UNKNOWN' if unresolved else 'NO', 'analysis': analysis,
            'searches': searches}


def length_schema(I, max_monoid=20000, max_checks=2000000):
    """Exact unary-language presentation of the whole comparison spectrum.

    A slice's term [a,b,e] denotes {e*m+(e-1)*n: m in Len(a),
    n in Len(b), n>0}. Len(a) is the language of path lengths from vertex 0
    to vertex a in the returned action graph. Unlike spectrum(), this does
    not stop after finding one unbounded term. None removes resource caps.
    """
    _check_limit(max_monoid, 'max_monoid')
    _check_limit(max_checks, 'max_checks')
    if not _validate(I):
        return {'status': 'UNSUPPORTED', 'reason': 'accepting states must be terminal'}
    slices, unresolved = [], False
    for f in sorted(I.final):
        normalized = boundary_slice(I, f)
        if normalized is None:
            continue
        J, _ = normalized
        try:
            generators, pair_ix, pair_of, sink = _combined_machine(J)
            monoid = ActionMonoid.build(generators, J.alphabet, max_monoid)
            counts = {'checks': 0, 'templates': 0}
            terms = sorted({(a,b,e) for _,a,b,e in
                            _terms(J, monoid, pair_ix, pair_of, sink, max_checks, counts)})
            slices.append({'final': f, 'status': 'COMPLETE', 'edges': monoid.edges,
                           'positive': [s is not None for s in monoid.positive],
                           'terms': terms})
        except ResourceLimit as error:
            unresolved = True
            slices.append({'final': f, 'status': 'UNKNOWN', 'reason': str(error)})
    return {'status': 'UNKNOWN' if unresolved else 'COMPLETE', 'slices': slices}


def spectrum_prefix(schema, max_length):
    """Exact spectrum intersection with [1,max_length], NOT a bounded word search.

    This is only valid for a COMPLETE length_schema. It places no cutoff on
    the gap word when its length has coefficient zero (the exponent-one case).
    """
    if not isinstance(max_length, int) or max_length < 0:
        raise ValueError('max_length must be a nonnegative integer')
    if schema['status'] != 'COMPLETE':
        raise ValueError('a complete length schema is required')
    answer = set()
    for item in schema['slices']:
        edges = item['edges']
        lengths = [set() for _ in edges]
        active = {0}
        for n in range(max_length+1):
            for a in active:
                lengths[a].add(n)
            active = {q for a in active for q in edges[a]}
        for a,b,e in item['terms']:
            if e == 1:
                # Existence of SOME positive v is all that matters here.
                if item['positive'][b]:
                    answer.update(lengths[a]-{0})
            else:
                answer.update(e*m+(e-1)*n for m in lengths[a]
                              for n in lengths[b] if n>0 and e*m+(e-1)*n<=max_length)
    return sorted(answer)
