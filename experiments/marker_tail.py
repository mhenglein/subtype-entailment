"""Exact fixed-marker-tail relaxation; this is not a general witness decider.

A target comparison is retained when its nonempty suffix contains at most H
copies of the word's final letter. All boundary failures are always retained.
The arbitrary prefix is allowed to revisit every original flag-target state.
The finite shared-reference construction adapts the target-frontier algorithm
at 6a13dfb; see notes/2026-09-08-semantic-marker-tails.md for proof and limits.
Python 3.9+, standard library only. No cap is interpreted as NO.
"""
from collections import deque
from dataclasses import dataclass
from itertools import product
from typing import Optional

from border_lab import Instance, witness, border_witness


class ResourceLimit(RuntimeError):
    """An unfinished finite computation, never a negative certificate."""


@dataclass(frozen=True)
class Limits:
    states: Optional[int] = 100000
    steps: Optional[int] = 1000000
    descriptors: Optional[int] = 100000
    schemas: Optional[int] = 20000
    blocks: Optional[int] = 8
    monoid: Optional[int] = 20000
    combinations: Optional[int] = 2000000

    def __post_init__(self):
        for name, value in self.__dict__.items():
            if value is not None and (type(value) is not int or value < 1):
                raise ValueError(name + ' must be a positive integer or None')


def check_cap(value, cap, message):
    if cap is not None and value > cap:
        raise ResourceLimit(message)


def validate(I):
    k = len(I.delta)
    if I.alphabet != '01' or k < 1 or type(I.start) is not int or not 0 <= I.start < k:
        raise ValueError('A nonempty binary Instance with a valid start is required')
    if any(len(row) != 2 or any(type(q) is not int or not -1 <= q < k for q in row)
           for row in I.delta):
        raise ValueError('Invalid partial transition table')
    if any(type(q) is not int or not 0 <= q < k for q in I.final | I.bad):
        raise ValueError('Invalid final/Bad state')
    if any(len(pair) != 2 or any(type(q) is not int or not 0 <= q < k for q in pair)
           for pair in I.flags):
        raise ValueError('Invalid flag')
    if any(any(q >= 0 for q in I.delta[f]) for f in I.final):
        raise ValueError('Terminal accepting states are required')


def reach(graph, starts):
    seen = set(starts)
    todo = list(starts)
    for p in todo:
        for q in graph[p]:
            if q >= 0 and q not in seen:
                seen.add(q)
                todo.append(q)
    return seen


def normalized_slice(I, final, last):
    """Boundary exclusion, terminal last-letter restriction, then exact trim."""
    bad = set(I.bad) | {p for p, q in I.flags if p == q or q == final}
    if I.start in bad or final in bad:
        return None
    table = [tuple(q if p not in bad and q not in bad and
                   (q != final or str(a) == last) else -1
                   for a, q in enumerate(row)) for p, row in enumerate(I.delta)]
    back = [[] for _ in table]
    for p, row in enumerate(table):
        for q in row:
            if q >= 0:
                back[q].append(p)
    live = sorted(reach(table, [I.start]) & reach(back, [final]))
    if I.start not in live:
        return None
    ix = {q: p for p, q in enumerate(live)}
    J = Instance(tuple(tuple(ix.get(q, -1) for q in table[p]) for p in live),
                 frozenset({ix[final]}),
                 frozenset((ix[p], ix[q]) for p, q in I.flags if p in ix and q in ix),
                 start=ix[I.start])
    return J, live


def tail_safe(I, word, H):
    """Independent word-level specification of the H-marker relaxation."""
    if type(H) is not int or H < 0:
        raise ValueError('H must be a nonnegative integer')
    if not I.admissible(word):
        return False
    c = I.run(word)
    n = len(word)
    if any((p, p) in I.flags or (p, c[-1]) in I.flags for p in c):
        return False
    if not word:
        return True
    b = word[-1]
    return not any((c[i], c[j]) in I.flags and word[j:].count(b) <= H
                   and word[i:].startswith(word[j:])
                   for i in range(n) for j in range(i+1, n))


def _plain_path(J):
    parent = {J.start: None}
    todo = deque([J.start])
    while todo:
        p = todo.popleft()
        if p in J.final:
            out = []
            while parent[p] is not None:
                p, a = parent[p]
                out.append(a)
            return ''.join(reversed(out))
        for a, q in enumerate(J.delta[p]):
            if q >= 0 and q not in parent:
                parent[q] = (p, str(a))
                todo.append(q)
    return None


def _pending(mask, eq, hits, r):
    out = 0
    for j in range(1, r):
        if mask >> j & 1 and eq >> j & 1:
            if j == r-1:
                return None
            out |= 1 << (j+1)
    if hits >> (r-1) & 1:
        return None
    for j in range(r-1):
        if hits >> j & 1:
            out |= 1 << (j+1)
    return out


def _observe(q, eq, hits, done, refs, flags):
    if not done:
        for j, rj in enumerate(refs):
            if rj >= 0 and eq >> j & 1 and (q, rj) in flags:
                hits |= 1 << j
    return hits


def _source_step(descriptors, columns, refs, pred, flags):
    out = set()
    for end, q, eq, hits, done in descriptors:
        options = [('_', q, True)]
        if not done:
            options.extend((a, p, False) for a, p in pred[q])
        for a, p, finished in options:
            e = eq
            for j, b in enumerate(columns):
                if a != b:
                    e &= ~(1 << j)
            h = _observe(p, e, hits, finished, refs, flags)
            out.add((end, p, e, h, finished))
    return frozenset(out)


def _observations(J, marker, descriptors, pred):
    reverse = [[p for _, p in row] for row in pred]
    closures = {}
    result = set()
    for end, q, eq, hits, done in descriptors:
        starts = {q}
        if not done:
            assert eq == 0
            if q not in closures:
                closures[q] = reach(reverse, [q])
            starts = closures[q]
        for start in starts:
            result.add((start, J.delta[end][marker], eq, hits, end))
    return result


def _prefix(J, cut, observations, equal, bit, r, allow, limits):
    def same(i, j):
        return i == j or bool(equal & bit[min(i,j), max(i,j)])
    forbidden = sum(1 << t for t in range(1, r)
                    if all(same(h, t+h) for h in range(r-t)))
    edges = {}
    for obs in sorted(observations):
        edges.setdefault(obs[0], []).append(obs)
    first = (J.start, 0)
    parent = {first: None}
    todo = deque([first])
    while todo:
        q, mask = state = todo.popleft()
        if q == cut and not mask & forbidden:
            out = []
            while parent[state] is not None:
                state, obs = parent[state]
                out.append(obs)
            return list(reversed(out))
        if not allow:
            continue
        for obs in edges.get(q, ()):
            nextmask = _pending(mask, obs[2], obs[3], r)
            nxt = (obs[1], nextmask)
            if nextmask is not None and nxt not in parent:
                check_cap(len(parent)+1, limits.states, 'Prefix state cap')
                parent[nxt] = (state, obs)
                todo.append(nxt)
    return None


def _recover(J, marker, schema, refs, desired, limits):
    """Unary source recovery with the proved max(reference lengths)+k bound."""
    start, target, eq, hits, end = desired
    data = 1-marker
    reftraces = []
    for (begin, stop, _), u in zip(schema, refs):
        path = [begin]
        for _ in u:
            path.append(J.delta[path[-1]][data])
        assert path[-1] == stop
        reftraces.append(path)
    path = [start]
    bound = max(map(len, refs), default=0) + len(J.delta)
    for length in range(bound+1):
        check_cap(length+1, limits.steps, 'Source reconstruction cap')
        if path[-1] == end:
            e = sum(1 << j for j, u in enumerate(refs) if length == len(u))
            h = 0
            for j, u in enumerate(refs):
                if any((path[length-t], reftraces[j][len(u)-t]) in J.flags
                       for t in range(min(length, len(u))+1)):
                    h |= 1 << j
            if (e, h) == (eq, hits):
                assert J.delta[end][marker] == target
                return str(data)*length
        nxt = J.delta[path[-1]][data]
        if nxt < 0:
            break
        path.append(nxt)
    raise AssertionError('Certified source observation has no realization')


def solve_schema(J, last, schema, allow_prefix, limits=Limits()):
    """Exact graph for the specified final blocks; no original target ban."""
    r = len(schema)
    marker = int(last)
    data = 1-marker
    pairs = tuple((i,j) for i in range(r) for j in range(i+1,r))
    bit = {p: 1 << j for j,p in enumerate(pairs)}
    guard = {p: sum(bit[p[0]+h,p[1]+h] for h in range(1,r-p[1])) for p in pairs}
    pred = [[] for _ in J.delta]
    for p,row in enumerate(J.delta):
        if row[data] >= 0:
            pred[row[data]].append((str(data),p))
    ends = [p for p,row in enumerate(J.delta) if row[marker] >= 0] if allow_prefix else []
    all_eq = (1 << len(pairs))-1
    src_eq = (1 << r)-1

    def ref_hit(coords, eq, hits):
        for i,j in pairs:
            if coords[i] >= 0 and coords[j] >= 0 and eq & bit[i,j]:
                if (coords[i],coords[j]) in J.flags:
                    hits |= bit[i,j]
        if any(hits & bit[p] and guard[p] == 0 for p in pairs):
            return None
        return hits

    coords = tuple(end for _,end,_ in schema)
    hits = ref_hit(coords, all_eq, 0)
    if hits is None:
        return dict(status='NO', states=0, steps=0)
    desc = frozenset((p,p,src_eq,_observe(p,src_eq,0,False,coords,J.flags),False) for p in ends)
    check_cap(len(desc), limits.descriptors, 'Initial descriptor cap')
    first = (coords,all_eq,hits,desc)
    parent = {first:None}
    todo = deque([first])
    steps = 0
    while todo:
        coords,eq,hits,desc = state = todo.popleft()
        if all(q < 0 for q in coords):
            if any(hits & bit[p] and eq & guard[p] == guard[p] for p in pairs):
                continue
            obs = _observations(J,marker,desc,pred)
            prefix = _prefix(J,schema[0][0],obs,eq,bit,r,allow_prefix,limits)
            if prefix is None:
                continue
            cols = []
            cursor = state
            while parent[cursor] is not None:
                cursor,col = parent[cursor]
                cols.append(col)
            # Parent traversal already reverses the reverse-reading columns.
            refs = tuple(''.join(col[j] for col in cols if col[j] != '_') for j in range(r))
            earlier = tuple(_recover(J,marker,schema,refs,o,limits) for o in prefix)
            word = ''.join(u+last for u in earlier+refs)
            assert len(earlier) <= len(J.delta)*(1 << (r-1))-1
            return dict(status='YES',word=word,states=len(parent),steps=steps,
                        prefix_blocks=len(earlier),reference_blocks=r)
        options = []
        for j,q in enumerate(coords):
            choices = [('_',-1)] if q < 0 else list(pred[q])
            if q >= 0 and q == schema[j][0]:
                choices.append(('_',-1))
            options.append(choices)
        for choices in product(*options):
            steps += 1
            check_cap(steps,limits.steps,'Reference transition cap')
            columns = tuple(a for a,_ in choices)
            nc = tuple(p for _,p in choices)
            ne = eq
            for i,j in pairs:
                if columns[i] != columns[j]:
                    ne &= ~bit[i,j]
            nh = ref_hit(nc,ne,hits)
            if nh is None:
                continue
            nd = _source_step(desc,columns,nc,pred,J.flags)
            check_cap(len(nd),limits.descriptors,'Source descriptor cap')
            nxt = (nc,ne,nh,nd)
            if nxt not in parent:
                check_cap(len(parent)+1,limits.states,'Reference state cap')
                parent[nxt] = (state,columns)
                todo.append(nxt)
    return dict(status='NO',states=len(parent),steps=steps)


def tail_schemas(J,last,H,limits):
    """r=H allows any prefix; r<H has NO prefix, covering all shorter words."""
    marker = int(last)
    data = 1-marker
    paths = [[row[data]] for row in J.delta]
    closure = [sorted(reach(paths,[p])) for p in range(len(paths))]
    seen = 0
    f = next(iter(J.final))
    for r in range(1,H+1):
        cuts = range(len(paths)) if r == H else [J.start]
        for cut in cuts:
            todo = [(cut,())]
            while todo:
                at,schema = todo.pop()
                seen += 1
                check_cap(seen,limits.schemas,'Schema-prefix cap')
                if at == f:
                    if len(schema) == r:
                        yield schema,r == H
                    continue
                if len(schema) >= r:
                    continue
                for end in reversed(closure[at]):
                    after = J.delta[end][marker]
                    if after >= 0:
                        todo.append((after,schema+((at,end,after),)))


def solve_slice(J,last,H,limits=Limits()):
    """Exact relaxation on a normalized, single-final, last-letter slice."""
    if type(H) is not int or H < 0 or last not in ('0','1'):
        raise ValueError('Nonnegative H and binary last letter required')
    if J.start in J.final or H == 0:
        word = _plain_path(J)
        return dict(status='NO') if word is None else dict(status='YES',word=word,schemas=0)
    count = 0
    try:
        check_cap(H,limits.blocks,'Requested marker-bound cap')
        for schema,allow in tail_schemas(J,last,H,limits):
            count += 1
            answer = solve_schema(J,last,schema,allow,limits)
            if answer['status'] == 'YES':
                assert tail_safe(J,answer['word'],H)
                return dict(answer,schemas=count)
    except ResourceLimit as error:
        return dict(status='UNKNOWN',reason=str(error),schemas=count)
    return dict(status='NO',schemas=count)


def relaxed_decision(I,H,limits=Limits()):
    """Decide existence for tail_safe, NOT for unrestricted Witness.

    An exhausted NO is also a sound unrestricted NO. YES only asserts the
    relaxation; actual_witness reports an independently checked stronger fact.
    """
    validate(I)
    if type(H) is not int or H < 0:
        raise ValueError('H must be nonnegative')
    if witness(I,''):
        return dict(status='YES',word='',actual_witness=True,slices=[])
    rows = []
    unknown = False
    for f in sorted(I.final):
        for last in '01':
            sliced = normalized_slice(I,f,last)
            if sliced is None:
                continue
            J,mapping = sliced
            ans = solve_slice(J,last,H,limits)
            rows.append(dict(final=f,last=last,local_to_input=mapping,result=ans))
            if ans['status'] == 'YES':
                w = ans['word']
                assert tail_safe(I,w,H)
                is_witness = witness(I,w)
                assert is_witness == border_witness(I,w)
                return dict(status='YES',word=w,actual_witness=is_witness,slices=rows)
            unknown |= ans['status'] == 'UNKNOWN'
    return dict(status='UNKNOWN' if unknown else 'NO',slices=rows)
