"""Exact marker costs of realizable last-aligned flagged suffix comparisons.

The joint-action template construction is the main-branch lastflag_spectrum
construction, restated here to keep the weighted graph primitive explicit.
Only positive-cost cycles imply unbounded marker count; zero-cost cycles may
have arbitrary word length. A bounded marker spectrum plus marker_tail gives
an exact decision for that certified slice, not for every terminal instance.
"""
from collections import deque

from border_lab import witness, border_witness
from marker_tail import (Limits, ResourceLimit, check_cap, normalized_slice,
                         reach, solve_slice, validate)


def _joint(J):
    k = len(J.delta)
    f = next(iter(J.final))
    pairs = [(p,q) for p in range(k) for q in range(k) if p != q and p != f]
    ids = {pair:k+i for i,pair in enumerate(pairs)}
    sink = k+len(pairs)
    letters = []
    for a in range(2):
        g = [row[a] if row[a] >= 0 else sink for row in J.delta]
        for p,q in pairs:
            dest = (J.delta[p][a],J.delta[q][a])
            g.append(ids.get(dest,sink) if dest not in J.flags else sink)
        g.append(sink)
        letters.append(tuple(g))
    return letters,ids,{i:pair for pair,i in ids.items()},sink


def _monoid(generators,limits):
    identity = tuple(range(len(generators[0])))
    actions = [identity]
    ids = {identity:0}
    reps = ['']
    positive = [None]
    edges = []
    at = 0
    while at < len(actions):
        row = []
        for a,g in enumerate(generators):
            effect = tuple(g[q] for q in actions[at])
            word = reps[at]+str(a)
            dest = ids.get(effect)
            if dest is None:
                check_cap(len(actions)+1,limits.monoid,'Joint action-monoid cap')
                dest = len(actions)
                ids[effect] = dest
                actions.append(effect)
                reps.append(word)
                positive.append(word)
            elif positive[dest] is None:
                positive[dest] = word
            row.append(dest)
        edges.append(tuple(row))
        at += 1
    return actions,edges,reps,positive


def _components(edges):
    """Iterative Kosaraju; the action graph is wholly reachable from zero."""
    n = len(edges)
    back = [[] for _ in edges]
    for p,row in enumerate(edges):
        for q in row:
            back[q].append(p)
    seen,order = set(),[]
    for root in range(n):
        if root in seen:
            continue
        seen.add(root)
        stack = [(root,0)]
        while stack:
            p,i = stack[-1]
            if i == len(edges[p]):
                order.append(p)
                stack.pop()
            else:
                q = edges[p][i]
                stack[-1] = (p,i+1)
                if q not in seen:
                    seen.add(q)
                    stack.append((q,0))
    comp = [-1]*n
    index = 0
    for root in reversed(order):
        if comp[root] >= 0:
            continue
        comp[root] = index
        stack = [root]
        while stack:
            p = stack.pop()
            for q in back[p]:
                if comp[q] < 0:
                    comp[q] = index
                    stack.append(q)
        index += 1
    return comp


def path_word(edges,start,target,allowed=None):
    parent = {start:None}
    todo = deque([start])
    while todo:
        p = todo.popleft()
        if p == target:
            word = []
            while parent[p] is not None:
                p,a = parent[p]
                word.append(a)
            return ''.join(reversed(word))
        for a,q in enumerate(edges[p]):
            if (allowed is None or q in allowed) and q not in parent:
                parent[q] = (p,str(a))
                todo.append(q)
    raise ValueError('No path between requested action vertices')


def weighted_fibres(edges,reps,cost_letters):
    """Maximum path cost or None, attaining words, and positive-cycle causes.

    Requires all vertices reachable from 0, as in a generated action graph.
    This is a complete finite graph calculation, with no word-length cutoff.
    """
    costs = tuple(int(str(a) in cost_letters) for a in range(2))
    comp = _components(edges)
    cause = {}
    todo = deque()
    for p,row in enumerate(edges):
        for a,q in enumerate(row):
            if costs[a] and comp[p] == comp[q] and p not in cause:
                cause[p] = (p,str(a),q)
                todo.append(p)
    while todo:
        p = todo.popleft()
        for q in edges[p]:
            if q not in cause:
                cause[q] = cause[p]
                todo.append(q)
    maximum = [-1]*len(edges)
    longest = [None]*len(edges)
    if 0 not in cause:
        maximum[0],longest[0] = 0,''
        todo = deque([0])
        queued = {0}
        while todo:
            p = todo.popleft()
            queued.remove(p)
            for a,q in enumerate(edges[p]):
                if q not in cause and maximum[q] < maximum[p]+costs[a]:
                    maximum[q] = maximum[p]+costs[a]
                    longest[q] = longest[p]+str(a)
                    if q not in queued:
                        todo.append(q)
                        queued.add(q)
    for p in cause:
        maximum[p] = None
    assert all(m is None or m >= 0 for m in maximum)
    return maximum,longest,cause,comp


def cost_lasso(edges,reps,target,cause,comp):
    p,a,q = cause[target]
    allowed = {v for v,c in enumerate(comp) if c == comp[p]}
    return dict(prefix=reps[p],loop=a+path_word(edges,q,p,allowed),
                suffix=path_word(edges,p,target))


def last_aligned(J,w,i,j):
    if not J.admissible(w) or not 0 <= i < j < len(w):
        return False
    c = J.run(w)
    f = c[-1]
    if any((p,p) in J.flags or (p,f) in J.flags for p in c):
        return False
    return ((c[i],c[j]) in J.flags and w[i:].startswith(w[j:]) and
            all((c[i+t],c[j+t]) not in J.flags for t in range(1,len(w)-j+1)))


def realize(certificate,m=1):
    if type(m) is not int or m < 1:
        raise ValueError('Pump exponent must be positive')
    u,v = certificate['u'],certificate['v']
    if 'pump' in certificate:
        p = certificate['pump']
        value = p['prefix']+p['loop']*m+p['suffix']
        if p['factor'] == 'u':
            u = value
        else:
            v = value
    x,e = certificate['head'],certificate['exponent']
    return dict(w=x+(u+v)*e+u,i=len(x),j=len(x)+len(u)+len(v))


def spectrum_slice(J,cost_letters,limits=Limits()):
    """Exact supremum for one normalized terminal slice; None means unbounded."""
    if any(a not in '01' for a in cost_letters) or len(set(cost_letters)) != len(cost_letters):
        raise ValueError('cost_letters must be a subset of 01')
    validate(J)
    if len(J.final) != 1 or J.bad:
        raise ValueError('One final state and prior boundary normalization required')
    f = next(iter(J.final))
    if any(p == q or q == f for p,q in J.flags):
        raise ValueError('Boundary normalization required')
    k = len(J.delta)
    sources = sorted({p for p,q in J.flags if p != q and p != f and q != f})
    if not sources:
        return dict(status='FINITE',H=0,templates=0,monoid_states=0,checks=0,
                    maximum_certificate=None)
    checks,terms,H = 0,0,0
    best = None
    try:
        generators,pair_ix,pair_of,sink = _joint(J)
        actions,edges,reps,positive = _monoid(generators,limits)
        maximum,longest,cause,comp = weighted_fibres(edges,reps,cost_letters)
        heads = {J.start:''}
        todo = deque([J.start])
        while todo:
            p = todo.popleft()
            for a,q in enumerate(J.delta[p]):
                if q >= 0 and q not in heads:
                    heads[q] = heads[p]+str(a)
                    todo.append(q)
        for ai,A in enumerate(actions):
            for bi,B in enumerate(actions):
                if positive[bi] is None:
                    continue
                for p in sources:
                    if p not in heads:
                        continue
                    checks += 1
                    check_cap(checks,limits.combinations,'Action-combination cap')
                    q = B[A[p]]
                    if (p,q) not in J.flags or (p,q) not in pair_ix:
                        continue
                    at = pair_ix[p,q]
                    for e in range(1,k):
                        end = A[at]
                        if end in pair_of and pair_of[end][1] == f:
                            terms += 1
                            cert = dict(head=heads[p],u=reps[ai],v=positive[bi],exponent=e)
                            ma,mb = maximum[ai],maximum[bi]
                            if ma is None or (e > 1 and mb is None):
                                factor,index = ('u',ai) if ma is None else ('v',bi)
                                cert['pump'] = dict(cost_lasso(edges,reps,index,cause,comp),factor=factor)
                                sample = realize(cert)
                                assert last_aligned(J,**sample)
                                assert any(a in cost_letters for a in cert['pump']['loop'])
                                return dict(status='UNBOUNDED',monoid_states=len(actions),checks=checks,
                                            templates=terms,pumping_certificate=cert)
                            value = e*ma+(e-1)*(mb if e > 1 else 0)
                            if value > H or best is None:
                                H = value
                                cert['u'] = longest[ai]
                                if e > 1:
                                    cert['v'] = longest[bi] or positive[bi]
                                sample = realize(cert)
                                assert last_aligned(J,**sample)
                                assert sum(a in cost_letters for a in sample['w'][sample['j']:]) == H
                                best = cert
                        at = B[A[at]]
                        if at == sink:
                            break
        return dict(status='FINITE',H=H,templates=terms,monoid_states=len(actions),checks=checks,
                    maximum_certificate=best)
    except ResourceLimit as error:
        return dict(status='UNKNOWN',reason=str(error),checks=checks,templates=terms)


def semantic_decision(I,limits=Limits()):
    """Exact when every nonempty final/last-letter slice has finite marker cost.

    One concrete witness suffices for YES. Any unbounded/capped unresolved slice
    prevents NO. Unbounded spectra alone say nothing about witness existence.
    """
    validate(I)
    if witness(I,''):
        return dict(status='YES',word='',slices=[])
    rows = []
    unknown = False
    for f in sorted(I.final):
        for last in '01':
            sliced = normalized_slice(I,f,last)
            if sliced is None:
                continue
            J,mapping = sliced
            analysis = spectrum_slice(J,last,limits)
            row = dict(final=f,last=last,local_to_input=mapping,analysis=analysis)
            rows.append(row)
            if analysis['status'] != 'FINITE':
                unknown = True
                continue
            result = solve_slice(J,last,analysis['H'],limits)
            row['search'] = result
            if result['status'] == 'YES':
                w = result['word']
                assert witness(I,w) and border_witness(I,w)
                return dict(status='YES',word=w,slices=rows)
            unknown |= result['status'] == 'UNKNOWN'
    return dict(status='UNKNOWN' if unknown else 'NO',slices=rows)
