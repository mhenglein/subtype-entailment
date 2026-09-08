"""Finite verifier and synthesizer for all-length three-way terminal NO certificates.

The verified rule covers a boundary-normalized binary terminal candidate language

    a^n b M a^m b a          (n >= 0, m >= 1)

with a regular middle M whose nonempty words begin with a. Unary runs need not
stabilize: finite transition orbits cover every residue. Middle words likewise
induce finitely many endpoint effects. Candidate-language equality is checked
exactly by DFA x epsilon-NFA symmetric difference.

`discover_three_way_certificate` removes the need to supply M manually. For
each orientation (a,b), it derives the maximal regular middle whose endpoint
states support every positive trailing a-power and then invokes the exact
verifier. Success is a genuine all-length NO certificate; failure is UNKNOWN.
"""
from collections import deque
from dataclasses import dataclass
from typing import FrozenSet, Tuple

from border_lab import Instance
from terminal_realization import validate


@dataclass(frozen=True)
class DFA:
    delta: Tuple[Tuple[int, int], ...]
    final: FrozenSet[int]
    start: int = 0

    def step(self,q,a):
        if q < 0: return -1
        return self.delta[q][a]


@dataclass(frozen=True)
class ThreeWayCertificate:
    a: int
    b: int
    middle: DFA


def _reachable_accepting(dfa,start):
    seen={start}; todo=[start]
    for q in todo:
        if q in dfa.final: return True
        for r in dfa.delta[q]:
            if r>=0 and r not in seen: seen.add(r); todo.append(r)
    return False


def _middle_starts_with_a(dfa,a,b):
    q=dfa.step(dfa.start,b)
    return q<0 or not _reachable_accepting(dfa,q)


def _positive_orbit(I,q,a):
    cur=I.delta[q][a]
    if cur<0: return None
    seen=set()
    while cur not in seen:
        if cur<0: return None
        seen.add(cur); cur=I.delta[cur][a]
        if cur<0: return None
    return frozenset(seen)


def _middle_effects(I,middle,q):
    first=(middle.start,q); seen={first}; todo=deque([first]); effects=set()
    while todo:
        m,p=todo.popleft()
        if m in middle.final: effects.add(p)
        for a in range(2):
            mm=middle.step(m,a)
            if mm<0: continue
            pp=I.delta[p][a] if p>=0 else -1
            nxt=(mm,pp)
            if nxt not in seen: seen.add(nxt); todo.append(nxt)
    return effects


def _epsilon_closure(states,middle):
    k=len(middle.delta); t0=1+k
    out=set(states); todo=list(states)
    while todo:
        s=todo.pop()
        if 1<=s<=k and (s-1) in middle.final and t0 not in out:
            out.add(t0); todo.append(t0)
    return frozenset(out)


def _family_step(states,letter,middle,a,b):
    k=len(middle.delta); t0,t1,post_b,fin=1+k,2+k,3+k,4+k
    out=set()
    for s in states:
        if s==0:
            if letter==a: out.add(0)
            if letter==b: out.add(1+middle.start)
        elif 1<=s<=k:
            q=middle.step(s-1,letter)
            if q>=0: out.add(1+q)
        elif s==t0:
            if letter==a: out.add(t1)
        elif s==t1:
            if letter==a: out.add(t1)
            if letter==b: out.add(post_b)
        elif s==post_b:
            if letter==a: out.add(fin)
    return _epsilon_closure(out,middle)


def _family_accepts(states,middle):
    return 4+len(middle.delta) in states


def _candidate_language_equal(I,middle,a,b):
    if len(I.final)!=1: return False,None
    f=next(iter(I.final)); nstart=_epsilon_closure({0},middle)
    first=(I.start,nstart); parent={first:None}; todo=deque([first])
    while todo:
        p,ns=state=todo.popleft()
        if (p==f)!=_family_accepts(ns,middle):
            letters=[]; cur=state
            while parent[cur] is not None:
                cur,x=parent[cur]; letters.append(str(x))
            return False,''.join(reversed(letters))
        for x in range(2):
            pp=I.delta[p][x] if p>=0 else -1
            nn=_family_step(ns,x,middle,a,b)
            nxt=(pp,nn)
            if nxt not in parent:
                parent[nxt]=(state,x); todo.append(nxt)
    return True,None


def verify_three_way_certificate(I,cert):
    """Verify the finite certificate; VERIFIED_NO is an all-length NO proof."""
    validate(I); a,b=cert.a,cert.b; middle=cert.middle
    if {a,b}!={0,1} or a==b:
        return {'status':'NOT_APPLICABLE','reason':'a,b must be the binary alphabet'}
    if len(I.final)!=1 or I.bad:
        return {'status':'NOT_APPLICABLE','reason':'Single terminal final and no Bad states required'}
    f=next(iter(I.final))
    if any(q>=0 for q in I.delta[f]):
        return {'status':'NOT_APPLICABLE','reason':'Final must be terminal'}
    if any(p==q or q==f for p,q in I.flags):
        return {'status':'NOT_APPLICABLE','reason':'Boundary-normalized flags required'}

    equal,counterexample=_candidate_language_equal(I,middle,a,b)
    if not equal:
        return {'status':'NOT_APPLICABLE','reason':'Candidate language does not equal certified family',
                'counterexample':counterexample}
    if not _middle_starts_with_a(middle,a,b):
        return {'status':'NOT_APPLICABLE','reason':'A nonempty middle word can start with b'}

    s0=I.start; leading=_positive_orbit(I,s0,a)
    if leading is None:
        return {'status':'NOT_APPLICABLE','reason':'Some positive leading a-power is undefined'}
    q0=I.delta[s0][b]
    if q0<0 or any(I.delta[p][b]!=q0 for p in leading):
        return {'status':'NOT_APPLICABLE','reason':'Leading a-orbit does not share one b-anchor',
                'leading_orbit':sorted(leading)}

    effects=_middle_effects(I,middle,q0)
    if not effects or -1 in effects:
        return {'status':'NOT_APPLICABLE','reason':'Accepted middle word is undefined from anchor control'}

    required={(s0,q) for q in effects}
    required|={(p,q) for p in leading for q in effects}
    rows=[]
    for q in sorted(effects):
        trailing=_positive_orbit(I,q,a)
        if trailing is None:
            return {'status':'NOT_APPLICABLE','reason':'Some positive trailing a-power is undefined',
                    'middle_effect':q}
        terminal_rows=[]
        for r in sorted(trailing):
            pre=I.delta[r][b]
            if pre<0 or I.delta[pre][a]!=f:
                return {'status':'NOT_APPLICABLE','reason':'Terminal ba suffix fails on a trailing orbit state',
                        'middle_effect':q,'trailing_state':r}
            required.add((s0,r)); terminal_rows.append((r,pre))
        rows.append({'middle_effect':q,'trailing_orbit':sorted(trailing),
                     'terminal_rows':terminal_rows})

    if not required.issubset(I.flags):
        return {'status':'NOT_APPLICABLE','reason':'Missing a required orbit-sensitive comparison flag',
                'required_flags':sorted(required),'missing_flags':sorted(required-I.flags)}

    return {'status':'VERIFIED_NO','family':'a* b M a+ b a',
            'leading_positive_orbit':sorted(leading),'post_b_anchor':q0,
            'middle_effects':rows,'required_flags':sorted(required),'final':f,
            'argument':{
              'n<m':'d=m-n>=1 selects delta(q,a^d) in the finite trailing orbit; compare from start',
              'n=m':'compare start with the middle endpoint q',
              'n>m':'d=n-m>=1 selects delta(start,a^d) in the finite leading orbit; compare with q'}}


def _universal_tail_states(I,a,b):
    """States q for which every q --a^m b a, m>=1, reaches the sole final."""
    if len(I.final)!=1: return frozenset()
    f=next(iter(I.final)); good=set()
    for q in range(len(I.delta)):
        orbit=_positive_orbit(I,q,a)
        if orbit is None: continue
        ok=True
        for r in orbit:
            pre=I.delta[r][b]
            if pre<0 or I.delta[pre][a]!=f:
                ok=False; break
        if ok: good.add(q)
    return frozenset(good)


def synthesize_three_way_certificate(I,a,b):
    """Derive the maximal middle supported by universal trailing a-powers."""
    if {a,b}!={0,1} or a==b or len(I.final)!=1:
        return None
    leading=_positive_orbit(I,I.start,a)
    if leading is None: return None
    q0=I.delta[I.start][b]
    if q0<0 or any(I.delta[p][b]!=q0 for p in leading): return None
    good=_universal_tail_states(I,a,b)
    if not good: return None
    return ThreeWayCertificate(a,b,DFA(tuple(tuple(row) for row in I.delta),good,q0))


def discover_three_way_certificate(I):
    """Automatic exact NO recognizer for the three-way orbit family.

    It tries both binary orientations. Failure to discover a certificate is
    INCONCLUSIVE; only VERIFIED_NO is a mathematical negative verdict.
    """
    attempts=[]
    for a,b in ((0,1),(1,0)):
        cert=synthesize_three_way_certificate(I,a,b)
        if cert is None:
            attempts.append({'a':a,'b':b,'status':'NO_SYNTHESIS'}); continue
        out=verify_three_way_certificate(I,cert)
        attempts.append({'a':a,'b':b,'status':out['status'],'reason':out.get('reason')})
        if out['status']=='VERIFIED_NO':
            return {'status':'VERIFIED_NO','a':a,'b':b,'certificate':cert,
                    'verification':out,'attempts':attempts}
    return {'status':'INCONCLUSIVE','attempts':attempts}
