"""Exact fixed-word-period three-way NO certificates.

Generalizes unary `a^n b M a^m b a` certificates to

    P^n B M P^m B P,   n>=0, m>=1,

for supplied nonempty binary words P and B and a regular middle language M.
All arithmetic cuts are at P-block boundaries. Exact candidate-language equality
is checked by DFA x epsilon-NFA symmetric difference. VERIFIED_NO is all-length;
failure is NOT_APPLICABLE/INCONCLUSIVE, never a negative guess.
"""
from collections import deque
from dataclasses import dataclass
from typing import FrozenSet, Tuple

from terminal_realization import validate
from three_way_cut_certificate import DFA


@dataclass(frozen=True)
class WordPeriodCertificate:
    period: str
    delimiter: str
    middle: DFA


def _run_word(delta,q,w):
    for a in w:
        if q < 0: return -1
        q=delta[q][int(a)]
    return q


def _positive_orbit_word(I,q,P):
    q=_run_word(I.delta,q,P)
    if q<0: return None
    seen=set()
    while q not in seen:
        if q<0: return None
        seen.add(q); q=_run_word(I.delta,q,P)
        if q<0: return None
    return frozenset(seen)


def _middle_effects(I,middle,q0):
    first=(middle.start,q0); seen={first}; todo=deque([first]); effects=set()
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


def _middle_nonempty_begins(middle,P):
    """Exact check L(M) subseteq {eps} union P Sigma*."""
    # status is matched prefix length 0..len(P), or -1 for mismatch.
    start=(middle.start,0); seen={start}; todo=deque([start])
    while todo:
        q,s=todo.popleft()
        if q in middle.final and s not in (0,len(P)):
            return False
        for a in range(2):
            qq=middle.step(q,a)
            if qq<0: continue
            ch=str(a)
            if s==-1: ss=-1
            elif s==len(P): ss=s
            elif ch==P[s]: ss=s+1
            else: ss=-1
            nxt=(qq,ss)
            if nxt not in seen: seen.add(nxt); todo.append(nxt)
    return True


class _NFA:
    def __init__(self):
        self.edges=[]; self.eps=[]
    def node(self):
        i=len(self.edges); self.edges.append([set(),set()]); self.eps.append(set()); return i
    def word(self,start,w,end=None):
        cur=start
        for i,ch in enumerate(w):
            nxt=end if end is not None and i==len(w)-1 else self.node()
            self.edges[cur][int(ch)].add(nxt); cur=nxt
        return cur
    def close(self,states):
        out=set(states); todo=list(out)
        while todo:
            p=todo.pop()
            for q in self.eps[p]:
                if q not in out: out.add(q); todo.append(q)
        return frozenset(out)
    def step(self,states,a):
        out=set()
        for p in self.close(states): out.update(self.edges[p][a])
        return self.close(out)


def _family_nfa(P,B,middle):
    nfa=_NFA(); s=nfa.node()
    # P* loop at leading boundary.
    nfa.word(s,P,s)
    after_b=nfa.word(s,B)
    # Embed middle DFA.
    mmap=[nfa.node() for _ in middle.delta]
    nfa.eps[after_b].add(mmap[middle.start])
    for q,row in enumerate(middle.delta):
        for a,r in enumerate(row):
            if r>=0: nfa.edges[mmap[q]][a].add(mmap[r])
    t0=nfa.node()
    for q in middle.final: nfa.eps[mmap[q]].add(t0)
    # Mandatory P+, then P*.
    t1=nfa.node(); nfa.word(t0,P,t1); nfa.word(t1,P,t1)
    after_b2=nfa.word(t1,B)
    accept=nfa.node(); nfa.word(after_b2,P,accept)
    return nfa,s,accept


def _candidate_language_equal(I,P,B,middle):
    if len(I.final)!=1: return False,None
    f=next(iter(I.final)); nfa,s,accept=_family_nfa(P,B,middle)
    first=(I.start,nfa.close({s})); parent={first:None}; todo=deque([first])
    while todo:
        p,ns=state=todo.popleft(); accepted=accept in ns
        if (p==f)!=accepted:
            chars=[]; cur=state
            while parent[cur] is not None:
                cur,a=parent[cur]; chars.append(str(a))
            return False,''.join(reversed(chars))
        for a in range(2):
            pp=I.delta[p][a] if p>=0 else -1
            nn=nfa.step(ns,a); nxt=(pp,nn)
            if nxt not in parent:
                parent[nxt]=(state,a); todo.append(nxt)
    return True,None


def verify_word_period_certificate(I,cert):
    validate(I); P,B,middle=cert.period,cert.delimiter,cert.middle
    if not P or not B or any(c not in '01' for c in P+B):
        return {'status':'NOT_APPLICABLE','reason':'P and B must be nonempty binary words'}
    if len(I.final)!=1 or I.bad:
        return {'status':'NOT_APPLICABLE','reason':'Single final and no Bad states required'}
    f=next(iter(I.final))
    if any(q>=0 for q in I.delta[f]) or any(p==q or q==f for p,q in I.flags):
        return {'status':'NOT_APPLICABLE','reason':'Terminal final and boundary-normalized flags required'}
    equal,counterexample=_candidate_language_equal(I,P,B,middle)
    if not equal:
        return {'status':'NOT_APPLICABLE','reason':'Candidate language differs from P* B M P+ B P family',
                'counterexample':counterexample}
    if not _middle_nonempty_begins(middle,P):
        return {'status':'NOT_APPLICABLE','reason':'A nonempty middle word does not begin with P'}

    leading=_positive_orbit_word(I,I.start,P)
    if leading is None:
        return {'status':'NOT_APPLICABLE','reason':'A positive leading P-power is undefined'}
    q0=_run_word(I.delta,I.start,B)
    if q0<0 or any(_run_word(I.delta,p,B)!=q0 for p in leading):
        return {'status':'NOT_APPLICABLE','reason':'Leading P-orbit does not share one B-anchor',
                'leading_orbit':sorted(leading)}
    effects=_middle_effects(I,middle,q0)
    if not effects or -1 in effects:
        return {'status':'NOT_APPLICABLE','reason':'Accepted middle word undefined from B-anchor'}

    required={(I.start,q) for q in effects}
    required|={(p,q) for p in leading for q in effects}
    rows=[]
    for q in sorted(effects):
        trailing=_positive_orbit_word(I,q,P)
        if trailing is None:
            return {'status':'NOT_APPLICABLE','reason':'A positive trailing P-power is undefined','effect':q}
        terminals=[]
        for r in sorted(trailing):
            pre=_run_word(I.delta,r,B)
            if pre<0 or _run_word(I.delta,pre,P)!=f:
                return {'status':'NOT_APPLICABLE','reason':'B P terminal cap fails on trailing P-orbit',
                        'effect':q,'trailing_state':r}
            required.add((I.start,r)); terminals.append((r,pre))
        rows.append({'middle_effect':q,'trailing_P_orbit':sorted(trailing),'terminal_rows':terminals})
    if not required.issubset(I.flags):
        return {'status':'NOT_APPLICABLE','reason':'Missing fixed-period comparison flags',
                'missing_flags':sorted(required-I.flags),'required_flags':sorted(required)}
    return {'status':'VERIFIED_NO','family':'P^n B M P^m B P','period':P,'delimiter':B,
            'leading_P_orbit':sorted(leading),'post_B_anchor':q0,'middle_effects':rows,
            'required_flags':sorted(required),
            'argument':{
              'n<m':'d=m-n>=1; r=delta(q,P^d); target P^n B P matches source prefix',
              'n=m':'flag(start,q); target P^n B P matches source prefix',
              'n>m':'d=n-m>=1; s=delta(start,P^d); source/target expose P^m B P'}}
