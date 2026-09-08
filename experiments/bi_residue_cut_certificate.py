"""Exact two-residue three-way symbolic NO certificates.

This extends orbit_split_cut_certificate so BOTH unary parameters may have
finite/ultimately-periodic domains. Candidate words are covered by decompositions

  a^n b u a^m b a,

where the leading b-edge selects a branch-specific middle anchor and the
trailing m is accepted exactly when the actual a-orbit from the chosen middle
endpoint can take b a to the sole final. The middle endpoint is existentially
chosen by a finite epsilon-NFA, but every accepted decomposition satisfies the
same n<m / n=m / n>m cut proof.

VERIFIED_NO is an all-length result. Failure is INCONCLUSIVE.
"""
from collections import deque

from terminal_realization import validate


def _prefix_orbit(I,start,a,positive=False):
    """Distinct states delta(start,a^d) until repeat/undefined."""
    seen=[]; q=start; d=0
    while q>=0 and q not in seen:
        if not positive or d>0: seen.append(q)
        q=I.delta[q][a]; d+=1
    return tuple(seen)


def _tail_capable(I,q,a,b,f):
    for r in _prefix_orbit(I,q,a,True):
        pre=I.delta[r][b]
        if pre>=0 and I.delta[pre][a]==f:
            return True
    return False


def _tail_capable_states(I,a,b,f):
    return frozenset(q for q in range(len(I.delta)) if _tail_capable(I,q,a,b,f))


def _reachable_subset(I,start,targets):
    seen={start}; todo=[start]; found=set()
    for p in todo:
        if p in targets: found.add(p)
        for q in I.delta[p]:
            if q>=0 and q not in seen:
                seen.add(q); todo.append(q)
    return frozenset(found)


def _middle_nonempty_starts_a(I,start,targets,b):
    q=I.delta[start][b]
    return q<0 or not _reachable_subset(I,q,targets)


def _close(states,tailcap):
    out=set(states)
    for s in tuple(out):
        if s[0]=='M' and s[1] in tailcap:
            out.add(('T0',s[1]))
    return frozenset(out)


def _family_step(I,states,letter,a,b,tailcap,f):
    states=_close(states,tailcap); out=set()
    for s in states:
        kind=s[0]
        if kind=='L':
            p=s[1]
            if letter==a and I.delta[p][a]>=0: out.add(('L',I.delta[p][a]))
            if letter==b and I.delta[p][b]>=0: out.add(('M',I.delta[p][b]))
        elif kind=='M':
            q=I.delta[s[1]][letter]
            if q>=0: out.add(('M',q))
        elif kind=='T0':
            if letter==a:
                q=I.delta[s[1]][a]
                if q>=0: out.add(('T1',q))
        elif kind=='T1':
            q=s[1]
            if letter==a:
                r=I.delta[q][a]
                if r>=0: out.add(('T1',r))
            if letter==b:
                r=I.delta[q][b]
                if r>=0: out.add(('B',r))
        elif kind=='B':
            if letter==a and I.delta[s[1]][a]==f: out.add(('F',))
    return _close(out,tailcap)


def _candidate_language_equal(I,a,b,tailcap,f):
    start=(I.start,_close({('L',I.start)},tailcap)); parent={start:None}; todo=deque([start])
    while todo:
        p,ns=state=todo.popleft(); accepted=('F',) in ns
        if (p==f)!=accepted:
            letters=[]; cur=state
            while parent[cur] is not None:
                cur,x=parent[cur]; letters.append(str(x))
            return False,''.join(reversed(letters))
        for x in range(2):
            pp=I.delta[p][x] if p>=0 else -1
            nn=_family_step(I,ns,x,a,b,tailcap,f); nxt=(pp,nn)
            if nxt not in parent:
                parent[nxt]=(state,x); todo.append(nxt)
    return True,None


def verify_bi_residue_certificate(I,a,b):
    validate(I)
    if {a,b}!={0,1} or a==b:
        return {'status':'NOT_APPLICABLE','reason':'a,b must be distinct binary letters'}
    if len(I.final)!=1 or I.bad:
        return {'status':'NOT_APPLICABLE','reason':'Single final and no Bad states required'}
    f=next(iter(I.final))
    if any(q>=0 for q in I.delta[f]) or any(p==q or q==f for p,q in I.flags):
        return {'status':'NOT_APPLICABLE','reason':'Terminal final and boundary-normalized flags required'}

    leading=_prefix_orbit(I,I.start,a,False)
    branches=tuple(p for p in leading if I.delta[p][b]>=0)
    if not branches:
        return {'status':'NOT_APPLICABLE','reason':'No leading residue has a b-anchor'}
    anchors={p:I.delta[p][b] for p in branches}
    tailcap=_tail_capable_states(I,a,b,f)
    if not tailcap:
        return {'status':'NOT_APPLICABLE','reason':'No state has an admissible positive trailing residue'}

    equal,counterexample=_candidate_language_equal(I,a,b,tailcap,f)
    if not equal:
        return {'status':'NOT_APPLICABLE','reason':'Candidate language differs from bi-residue family',
                'counterexample':counterexample}

    effects={}
    for p,q0 in anchors.items():
        if not _middle_nonempty_starts_a(I,q0,tailcap,b):
            return {'status':'NOT_APPLICABLE','reason':'A branch has a nonempty middle beginning with b',
                    'leading_state':p,'anchor':q0}
        effects[p]=_reachable_subset(I,q0,tailcap)
        if not effects[p]:
            return {'status':'NOT_APPLICABLE','reason':'A leading branch has no tail-capable middle endpoint',
                    'leading_state':p,'anchor':q0}

    positive_leading=frozenset(_prefix_orbit(I,I.start,a,True))
    required=set(); rows=[]
    for p in branches:
        erows=[]
        for q in sorted(effects[p]):
            trailing_prefix=frozenset(_prefix_orbit(I,q,a,True))
            accepted_tail=[]
            for r in trailing_prefix:
                pre=I.delta[r][b]
                if pre>=0 and I.delta[pre][a]==f: accepted_tail.append(r)
            if not accepted_tail:
                raise AssertionError('Tail-capable effect lost its accepting residue')
            required.add((I.start,q))
            required.update((I.start,r) for r in trailing_prefix)
            required.update((s,q) for s in positive_leading)
            erows.append({'effect':q,'positive_a_orbit':sorted(trailing_prefix),
                          'terminal_residue_states':sorted(accepted_tail)})
        rows.append({'leading_state':p,'anchor':anchors[p],'effects':erows})

    if not required.issubset(I.flags):
        return {'status':'NOT_APPLICABLE','reason':'Missing bi-residue comparison flags',
                'missing_flags':sorted(required-I.flags),'required_flags':sorted(required)}

    return {'status':'VERIFIED_NO','family':'a^n b M_{p_n} a^m b a',
            'leading_parameter':'defined b-edges on finite/eventually-periodic a-orbit',
            'trailing_parameter':'for each effect q, m>=1 with delta(q,a^m b a)=final; finite/eventually-periodic',
            'leading_trajectory':list(leading),'active_leading_states':list(branches),
            'anchors':anchors,'tail_capable_states':sorted(tailcap),'branches':rows,
            'required_flags':sorted(required),
            'argument':{
              'n<m':'d=m-n>=1; r=delta(q,a^d); flag(start,r)',
              'n=m':'flag(start,q)',
              'n>m':'d=n-m>=1; s=delta(start,a^d); flag(s,q)'}}


def discover_bi_residue_certificate(I):
    attempts=[]
    for a,b in ((0,1),(1,0)):
        out=verify_bi_residue_certificate(I,a,b)
        attempts.append({'a':a,'b':b,'status':out['status'],'reason':out.get('reason')})
        if out['status']=='VERIFIED_NO':
            return {'status':'VERIFIED_NO','a':a,'b':b,'verification':out,'attempts':attempts}
    return {'status':'INCONCLUSIVE','attempts':attempts}
