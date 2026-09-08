"""Exact orbit-split three-way symbolic NO certificates.

Generalizes three_way_cut_certificate by allowing the delimiter after the
leading a^n block to reach different anchors on different finite a-orbit
states. The candidate family is checked exactly as

  a^n b M_{p_n} a^m b a,  n>=0, m>=1,

where p_n=delta(start,a^n) and M_p is a regular middle language from the
branch-specific b-anchor. The same n<m / n=m / n>m cut proof then uses finite
leading/trailing state orbits. VERIFIED_NO is all-length; failure is UNKNOWN.
"""
from collections import deque

from border_lab import Instance
from terminal_realization import validate
from three_way_cut_certificate import _positive_orbit


def _universal_tail_states(I,a,b):
    if len(I.final)!=1: return frozenset()
    f=next(iter(I.final)); good=set()
    for q in range(len(I.delta)):
        orbit=_positive_orbit(I,q,a)
        if orbit is None: continue
        if all(I.delta[r][b]>=0 and I.delta[I.delta[r][b]][a]==f for r in orbit):
            good.add(q)
    return frozenset(good)


def _leading_states(I,a):
    """All states delta(start,a^n), n>=0, or None if some power is undefined."""
    seen=[]; q=I.start
    while q not in seen:
        if q<0: return None
        seen.append(q); q=I.delta[q][a]
    return tuple(seen)


def _reachable_good(I,start,good):
    seen={start}; todo=[start]; out=set()
    for p in todo:
        if p in good: out.add(p)
        for q in I.delta[p]:
            if q>=0 and q not in seen:
                seen.add(q); todo.append(q)
    return frozenset(out)


def _middle_nonempty_starts_a(I,start,good,b):
    """No accepted middle word with first symbol b."""
    q=I.delta[start][b]
    if q<0: return True
    return not _reachable_good(I,q,good)


def _family_step(I, states, letter, a, b, good):
    """epsilon-NFA step for the orbit-split family.

    states are tagged tuples:
      ('L',p) leading a* at original control p
      ('M',q) middle control
      ('T0',) before mandatory trailing a+
      ('T1',) inside trailing a+
      ('B',) after final b
      ('F',) accepting after final a
    Epsilon M->T0 is closed before and after consuming a symbol.
    """
    def close(xs):
        out=set(xs)
        if any(tag[0]=='M' and tag[1] in good for tag in tuple(out)):
            out.add(('T0',))
        return frozenset(out)
    states=close(states); out=set()
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
            if letter==a: out.add(('T1',))
        elif kind=='T1':
            if letter==a: out.add(('T1',))
            if letter==b: out.add(('B',))
        elif kind=='B':
            if letter==a: out.add(('F',))
    return close(out)


def _candidate_language_equal(I,a,b,good):
    """Exact DFA x finite-subset-NFA symmetric-difference emptiness."""
    start=(I.start,frozenset({('L',I.start)})); parent={start:None}; todo=deque([start])
    f=next(iter(I.final))
    while todo:
        p,ns=state=todo.popleft()
        accepted=('F',) in ns
        if (p==f)!=accepted:
            letters=[]; cur=state
            while parent[cur] is not None:
                cur,x=parent[cur]; letters.append(str(x))
            return False,''.join(reversed(letters))
        for x in range(2):
            pp=I.delta[p][x] if p>=0 else -1
            nn=_family_step(I,ns,x,a,b,good)
            nxt=(pp,nn)
            if nxt not in parent:
                parent[nxt]=(state,x); todo.append(nxt)
    return True,None


def verify_orbit_split_certificate(I,a,b):
    validate(I)
    if {a,b}!={0,1} or a==b:
        return {'status':'NOT_APPLICABLE','reason':'a,b must be distinct binary letters'}
    if len(I.final)!=1 or I.bad:
        return {'status':'NOT_APPLICABLE','reason':'Single final and no Bad states required'}
    f=next(iter(I.final))
    if any(q>=0 for q in I.delta[f]) or any(p==q or q==f for p,q in I.flags):
        return {'status':'NOT_APPLICABLE','reason':'Terminal final and boundary-normalized flags required'}
    leading=_leading_states(I,a)
    if leading is None:
        return {'status':'NOT_APPLICABLE','reason':'Leading a-powers are not all defined'}
    anchors={p:I.delta[p][b] for p in leading}
    if any(q<0 for q in anchors.values()):
        return {'status':'NOT_APPLICABLE','reason':'Some leading orbit state has no b-anchor'}
    good=_universal_tail_states(I,a,b)
    if not good:
        return {'status':'NOT_APPLICABLE','reason':'No universal trailing-tail states'}
    equal,counterexample=_candidate_language_equal(I,a,b,good)
    if not equal:
        return {'status':'NOT_APPLICABLE','reason':'Candidate language differs from orbit-split family',
                'counterexample':counterexample}
    effects={}
    for p,q0 in anchors.items():
        if not _middle_nonempty_starts_a(I,q0,good,b):
            return {'status':'NOT_APPLICABLE','reason':'A branch has a nonempty middle beginning with b',
                    'leading_state':p,'anchor':q0}
        effects[p]=_reachable_good(I,q0,good)
        if not effects[p]:
            return {'status':'NOT_APPLICABLE','reason':'A leading branch has no middle effect',
                    'leading_state':p,'anchor':q0}

    positive=_positive_orbit(I,I.start,a)
    if positive is None:
        return {'status':'NOT_APPLICABLE','reason':'Positive leading orbit undefined'}
    required=set(); rows=[]
    for p in leading:
        erows=[]
        for q in sorted(effects[p]):
            required.add((I.start,q)) # n=m
            trailing=_positive_orbit(I,q,a)
            if trailing is None:
                return {'status':'NOT_APPLICABLE','reason':'Trailing orbit undefined','effect':q}
            for r in trailing:
                required.add((I.start,r)) # n<m
            for dstate in positive:
                required.add((dstate,q)) # n>m
            erows.append({'effect':q,'trailing_orbit':sorted(trailing)})
        rows.append({'leading_state':p,'anchor':anchors[p],'effects':erows})
    if not required.issubset(I.flags):
        return {'status':'NOT_APPLICABLE','reason':'Missing orbit-split comparison flags',
                'missing_flags':sorted(required-I.flags),'required_flags':sorted(required)}
    return {'status':'VERIFIED_NO','family':'a^n b M_{p_n} a^m b a',
            'leading_states':list(leading),'anchors':anchors,'good_states':sorted(good),
            'branches':rows,'required_flags':sorted(required),
            'argument':{
              'n<m':'r=delta(q,a^(m-n)); flag(start,r); target is a^n b a',
              'n=m':'flag(start,q); target is a^n b a',
              'n>m':'s=delta(start,a^(n-m)); flag(s,q); both expose a^m b a'}}


def discover_orbit_split_certificate(I):
    attempts=[]
    for a,b in ((0,1),(1,0)):
        out=verify_orbit_split_certificate(I,a,b)
        attempts.append({'a':a,'b':b,'status':out['status'],'reason':out.get('reason')})
        if out['status']=='VERIFIED_NO':
            return {'status':'VERIFIED_NO','a':a,'b':b,'verification':out,'attempts':attempts}
    return {'status':'INCONCLUSIVE','attempts':attempts}
