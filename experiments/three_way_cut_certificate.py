"""Finite verifier for a reusable all-length terminal NO certificate.

The rule covers a boundary-normalized binary terminal candidate language

    a^n b M a^m b a          (n >= 0, m >= 1)

where M is supplied by a DFA, every nonempty M-word starts with a, and M acts
as a loop at the post-b control state.  Three fixed flags then cover n<m,
n=m,n>m respectively.  Candidate-language equality is verified exactly by a
DFA x epsilon-NFA symmetric-difference search, so this is a finite proof object,
not a bounded-word heuristic.

See notes/2026-09-08-three-way-cut-certificates.md.
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
    """Every accepted nonempty middle word begins with a."""
    q=dfa.step(dfa.start,b)
    return q<0 or not _reachable_accepting(dfa,q)


def _middle_loops_control(I,middle,q):
    """Every u in L(middle) is defined from q and returns exactly to q."""
    first=(middle.start,q); seen={first}; todo=deque([first])
    while todo:
        m,p=todo.popleft()
        if m in middle.final and p!=q: return False
        for a in range(2):
            mm=middle.step(m,a)
            if mm<0: continue
            pp=I.delta[p][a] if p>=0 else -1
            nxt=(mm,pp)
            if nxt not in seen: seen.add(nxt); todo.append(nxt)
    return True


def _epsilon_closure(states,middle):
    # NFA integer layout: L=0, M(q)=1+q, T0=1+k, T1=2+k, B=3+k, F=4+k.
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
    """Exact L(I,start->final) == a* b M a+ b a check."""
    if len(I.final)!=1: return False,None
    f=next(iter(I.final))
    nstart=_epsilon_closure({0},middle)
    first=(I.start,nstart); parent={first:None}; todo=deque([first])
    while todo:
        p,ns=state=todo.popleft()
        left=(p==f); right=_family_accepts(ns,middle)
        if left!=right:
            # Return a concrete symmetric-difference witness for diagnostics.
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
    """Verify the finite certificate and return structural proof data.

    A VERIFIED result proves that the terminal candidate language has no
    witness.  Any failed premise is NOT_APPLICABLE; it is never interpreted NO.
    """
    validate(I)
    a,b=cert.a,cert.b; middle=cert.middle
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

    # Infer the five distinguished control states from the actual transition
    # table and verify the parametric run invariants used by the three cases.
    s0=I.start; s1=I.delta[s0][a]
    if s1<0 or I.delta[s1][a]!=s1:
        return {'status':'NOT_APPLICABLE','reason':'Leading a+ does not stabilize'}
    q0=I.delta[s0][b]
    if q0<0 or I.delta[s1][b]!=q0:
        return {'status':'NOT_APPLICABLE','reason':'Leading b does not share a control state'}
    if not _middle_loops_control(I,middle,q0):
        return {'status':'NOT_APPLICABLE','reason':'Middle language does not loop the anchor control'}
    q1=I.delta[q0][a]
    if q1<0 or I.delta[q1][a]!=q1:
        return {'status':'NOT_APPLICABLE','reason':'Trailing a+ does not stabilize'}
    q2=I.delta[q1][b]
    if q2<0 or I.delta[q2][a]!=f:
        return {'status':'NOT_APPLICABLE','reason':'Terminal ba suffix is not forced'}

    required={(s0,q1),(s0,q0),(s1,q0)}
    if not required.issubset(I.flags):
        return {'status':'NOT_APPLICABLE','reason':'Missing one of the three comparison flags',
                'required_flags':sorted(required)}

    return {'status':'VERIFIED_NO','family':'a* b M a+ b a',
            'states':{'source_start':s0,'source_inside':s1,
                      'target_start':q0,'target_inside':q1,'pre_final':q2,'final':f},
            'case_flags':{'n<m':(s0,q1),'n=m':(s0,q0),'n>m':(s1,q0)},
            'argument':{
              'n<m':'compare source at 0 with target after m-n trailing a symbols; both begin a^n b a',
              'n=m':'compare source at 0 with start of trailing a-run; both begin a^n b a',
              'n>m':'compare source at n-m with start of trailing a-run; both begin a^m b a'}}
