#!/usr/bin/env python3
"""Exact synthesis for regularly switched copies of marked terminal suffixes.

This is a complete algorithm for the supplied description, NOT a general
BorderAvoid solver. With no caps it exhausts finite transformation monoids and
finite control graphs. A cap returns UNKNOWN. All data words share one assignment.
Python 3.10+, standard library only.
"""
from __future__ import annotations
from dataclasses import dataclass
from collections import deque
from itertools import product
import argparse
import json
from typing import Optional, Sequence

Word = tuple[int, ...]

@dataclass(frozen=True)
class DFA:
    delta: tuple[tuple[int, ...], ...]
    start: int
    finals: frozenset[int]

    def __post_init__(self):
        n = len(self.delta)
        if not n or type(self.start) is not int or not 0 <= self.start < n:
            raise ValueError('DFA needs valid nonempty states and start')
        a = len(self.delta[0])
        if not a or any(len(row) != a for row in self.delta):
            raise ValueError('DFA rows must have the same nonzero alphabet size')
        if any(type(q) is not int or q < -1 or q >= n for row in self.delta for q in row):
            raise ValueError('DFA transitions must be state numbers or -1')
        if any(type(q) is not int or not 0 <= q < n for q in self.finals):
            raise ValueError('Invalid accepting state')

    @property
    def n(self): return len(self.delta)
    @property
    def alphabet(self): return len(self.delta[0])

    def run(self, w: Sequence[int], start: Optional[int] = None):
        q = self.start if start is None else start
        if not 0 <= q < self.n: raise ValueError('Invalid run start')
        path = [q]
        for a in w:
            if type(a) is not int or not 0 <= a < self.alphabet:
                raise ValueError('Word contains an invalid symbol')
            q = self.delta[q][a]
            if q < 0: return None
            path.append(q)
        return tuple(path)

    def accepts(self, w):
        c = self.run(w)
        return c is not None and c[-1] in self.finals

    def as_json(self):
        return dict(delta=self.delta, start=self.start, finals=sorted(self.finals))


def universal(alphabet: int) -> DFA:
    return DFA((tuple(0 for _ in range(alphabet)),), 0, frozenset({0}))


def finite_language(words: Sequence[Word], alphabet: int) -> DFA:
    rows = [[-1] * alphabet]
    ends = set()
    for w in sorted(set(words)):
        q = 0
        for a in w:
            if type(a) is not int or not 0 <= a < alphabet:
                raise ValueError('Invalid symbol in finite language')
            if rows[q][a] == -1:
                rows[q][a] = len(rows); rows.append([-1] * alphabet)
            q = rows[q][a]
        ends.add(q)
    return DFA(tuple(map(tuple, rows)), 0, frozenset(ends))


@dataclass(frozen=True)
class Edge:
    source: int
    kind: int           # 0-based reference index j
    target: int
    guard: DFA          # accepts T_j, excluding the END delimiter


@dataclass(frozen=True)
class Description:
    references: int
    controls: int
    start: int
    finals: frozenset[int]
    edges: tuple[Edge, ...]
    master_guard: DFA   # accepts T_0, excluding SWITCH and END
    output_guard: DFA   # accepts the complete token word

    def __post_init__(self):
        if type(self.references) is not int or self.references < 1:
            raise ValueError('Positive reference count required')
        if type(self.controls) is not int or self.controls < 1 or not 0 <= self.start < self.controls:
            raise ValueError('Invalid finite control')
        if not self.finals <= set(range(self.controls)):
            raise ValueError('Invalid control final')
        keys = set()
        for e in self.edges:
            if not (0 <= e.source < self.controls and 0 <= e.target < self.controls
                    and 0 <= e.kind < self.references): raise ValueError('Invalid control edge')
            if (e.source, e.kind) in keys: raise ValueError('Control must be deterministic by kind')
            keys.add((e.source, e.kind))
        if any(d.alphabet != self.alphabet for d in
               [self.master_guard, self.output_guard] + [e.guard for e in self.edges]):
            raise ValueError('All guard alphabets must match the token alphabet')

    @property
    def alphabet(self): return self.references + 4
    @property
    def end(self): return self.references + 2
    @property
    def switch(self): return self.references + 3
    def marker(self, j): return 2 + j

    def as_json(self):
        return dict(references=self.references, controls=self.controls, start=self.start,
                    finals=sorted(self.finals),
                    edges=[dict(source=e.source,kind=e.kind,target=e.target,guard=e.guard.as_json())
                           for e in self.edges], master_guard=self.master_guard.as_json(),
                    output_guard=self.output_guard.as_json())


@dataclass(frozen=True)
class Instance:
    machine: DFA
    flags: frozenset[tuple[int, int]]

    def __post_init__(self):
        if any(any(q != -1 for q in self.machine.delta[f]) for f in self.machine.finals):
            raise ValueError('Instance accepting states must be terminal')
        if any(not (0 <= p < self.machine.n and 0 <= t < self.machine.n) for p,t in self.flags):
            raise ValueError('Invalid flag')


def witness_direct(I: Instance, w: Word) -> bool:
    c = I.machine.run(w)
    if c is None or c[-1] not in I.machine.finals: return False
    n = len(w)
    for i,p in enumerate(c):
        for j in range(i,n+1):
            if (p,c[j]) in I.flags and w[i:i+n-j] == w[j:]: return False
    return True


def witness_reverse(I: Instance, w: Word) -> bool:
    c = I.machine.run(w)
    if c is None or c[-1] not in I.machine.finals: return False
    rev, states = w[::-1],c[::-1]
    for length in range(len(w)+1):
        for border in range(length+1):
            if ((states[length],states[border]) in I.flags
                    and rev[:border] == rev[length-border:length]): return False
    return True


def suffixes(D: Description, data: Sequence[Word]) -> tuple[Word, ...]:
    if len(data) != D.references or any(a not in (0,1) for x in data for a in x):
        raise ValueError('Supply one binary data word per reference')
    tails = [()] * D.references
    rest = ()
    for j in reversed(range(D.references)):
        rest = (D.marker(j),) + tuple(data[j]) + rest
        tails[j] = rest
    return tuple(tails)


def materialize(D: Description, data: Sequence[Word], sequence: Sequence[int]) -> Word:
    tails = suffixes(D,data)
    if any(type(j) is not int or not 0 <= j < D.references for j in sequence):
        raise ValueError('Invalid reference in sequence')
    return sum((tails[j]+(D.end,) for j in sequence),()) + (D.switch,) + tails[0]+(D.end,)


def semantic_witness(D: Description, w: Word) -> bool:
    """Independent parser and equality specification; no compiled flags used."""
    if w.count(D.switch) != 1: return False
    cut = w.index(D.switch)
    prefix, master = w[:cut],w[cut+1:]
    if not master or master[-1] != D.end or D.end in master[:-1]: return False
    master = master[:-1]
    def parse(unit,first):
        k=0; out=[]
        for j in range(first,D.references):
            if k == len(unit) or unit[k] != D.marker(j): return None
            k += 1; beg=k
            while k < len(unit) and unit[k] in (0,1): k += 1
            out.append(unit[beg:k])
        return tuple(out) if k == len(unit) else None
    v = parse(master,0)
    if v is None or not D.master_guard.accepts(master): return False
    tails = suffixes(D,v)
    control=D.start; left=0
    es={(e.source,e.kind):e for e in D.edges}
    while left < len(prefix):
        try: right=prefix.index(D.end,left)
        except ValueError: return False
        unit=prefix[left:right]
        if not unit: return False
        kind=unit[0]-2
        if not 0 <= kind < D.references or parse(unit,kind) is None: return False
        e=es.get((control,kind))
        if e is None or not e.guard.accepts(unit) or unit != tails[kind]: return False
        control=e.target;left=right+1
    return control in D.finals and D.output_guard.accepts(w)


def compile_tokens(D: Description) -> Instance:
    """Build the actual partial DFA, including all regular guards, and G.

    Original parser states carry a predecessor token after a token of a unit or
    master. There are no source/target annotations at the pre-marker boundary.
    Unique initial markers rule out distinct comparable whole-word suffixes.
    """
    a,h=D.alphabet,D.references
    edges={(e.source,e.kind):(i,e) for i,e in enumerate(D.edges)}
    def step(p,sym):
        mode=p[0]
        if mode=='out':
            r=p[1]
            if sym==D.switch and r in D.finals:return ('master-start',)
            j=sym-2
            item=edges.get((r,j))
            if item is not None:
                i,e=item;q=e.guard.delta[e.guard.start][sym]
                if q>=0:return ('unit',i,j,q,sym)
        elif mode=='master-start':
            if sym==D.marker(0):
                q=D.master_guard.delta[D.master_guard.start][sym]
                if q>=0:return ('master',0,q,sym)
        elif mode in ('unit','master'):
            if mode=='unit':
                _,ei,t,q,last=p;guard=D.edges[ei].guard
            else:
                _,t,q,last=p;guard=D.master_guard
            if sym==D.end:
                if t==h-1 and q in guard.finals:
                    return ('out',D.edges[ei].target) if mode=='unit' else ('final',)
            elif sym in (0,1) or (t<h-1 and sym==D.marker(t+1)):
                nxt=guard.delta[q][sym]
                if nxt>=0:
                    tt=t+int(sym not in (0,1))
                    return ('unit',ei,tt,nxt,sym) if mode=='unit' else ('master',tt,nxt,sym)
        return None
    def annotation(p):
        if p[0]=='unit':return ('s',D.edges[p[1]].kind,p[-1])
        if p[0]=='master':return ('t',p[1],p[-1])
        return None
    first=(('out',D.start),D.output_guard.start)
    states=[first];ids={first:0};rows=[];tags=[];finals=set()
    at=0
    while at<len(states):
        p,m=states[at]
        tags.append(annotation(p))
        if p==('final',) and m in D.output_guard.finals:finals.add(at)
        row=[]
        for sym in range(a):
            pp=step(p,sym);mm=D.output_guard.delta[m][sym]
            if pp is None or mm<0:row.append(-1);continue
            nxt=(pp,mm)
            if nxt not in ids:ids[nxt]=len(states);states.append(nxt)
            row.append(ids[nxt])
        rows.append(tuple(row));at+=1
    sources=[(q,t) for q,t in enumerate(tags) if t is not None and t[0]=='s']
    targets=[(q,t) for q,t in enumerate(tags) if t is not None and t[0]=='t']
    G=frozenset((p,q) for p,s in sources for q,t in targets if s[1]<=t[1] and s[2]!=t[2])
    return Instance(DFA(tuple(rows),0,frozenset(finals)),G)


def compile_binary(I: Instance) -> tuple[Instance, tuple[Word,...]]:
    """Fixed-length injective token code. Only token-boundary states are flagged."""
    alphabet=I.machine.alphabet
    width=max(1,(alphabet-1).bit_length())
    code=tuple(tuple(map(int,format(a,f'0{width}b'))) for a in range(alphabet))
    n=I.machine.n;rows=[[-1,-1] for _ in range(n)]
    for p in range(n):
        for a,dest in enumerate(I.machine.delta[p]):
            if dest<0:continue
            q=p
            for bit in code[a][:-1]:
                if rows[q][bit]<0:rows[q][bit]=len(rows);rows.append([-1,-1])
                q=rows[q][bit]
            bit=code[a][-1]
            if rows[q][bit] not in (-1,dest):raise AssertionError('Decoder conflict')
            rows[q][bit]=dest
    return Instance(DFA(tuple(map(tuple,rows)),I.machine.start,I.machine.finals),I.flags),code


def encode(w: Word, code: tuple[Word,...]) -> Word:
    return sum((code[a] for a in w),())


def compose(A: tuple[int,...],B: tuple[int,...]) -> tuple[int,...]:
    """Reading the word for A followed by the word for B."""
    return tuple(B[q] for q in A)


class JointActions:
    def __init__(self, automata: Sequence[DFA]):
        self.ds=tuple(automata);self.offsets=[];n=0
        for d in self.ds:self.offsets.append(n);n+=d.n
        self.sink=n;self.n=n+1;self.identity=tuple(range(self.n))
        letters=[]
        for a in range(self.ds[0].alphabet):
            row=[]
            for off,d in zip(self.offsets,self.ds):
                row.extend(off+r[a] if r[a]>=0 else self.sink for r in d.delta)
            row.append(self.sink);letters.append(tuple(row))
        self.letters=tuple(letters)

    def start(self,i):return self.offsets[i]+self.ds[i].start
    def accepting(self,i,q):return q-self.offsets[i] in self.ds[i].finals

    def enumerate_data(self,cap=None):
        actions=[self.identity];representatives=[()];ids={self.identity:0}
        at=0
        while at<len(actions):
            for a in (0,1):
                nxt=compose(actions[at],self.letters[a])
                if nxt not in ids:
                    if cap is not None and len(actions)>=cap:return None
                    ids[nxt]=len(actions);actions.append(nxt)
                    representatives.append(representatives[at]+(a,))
            at+=1
        return tuple(actions),tuple(representatives)


def solve(D: Description, *, max_actions=None, max_tuples=None) -> dict:
    """Complete finite solver; optional caps only produce UNKNOWN, never NO."""
    for v in (max_actions,max_tuples):
        if v is not None and (type(v) is not int or v<1):raise ValueError('Caps must be positive or None')
    guards=[e.guard for e in D.edges]+[D.master_guard,D.output_guard]
    J=JointActions(guards);mi=len(D.edges);oi=mi+1
    enumeration=J.enumerate_data(max_actions)
    if enumeration is None:return dict(status='UNKNOWN',reason='action cap',exhausted=False)
    actions,reps=enumeration;h=D.references;checked=0;graphs=0;nodes_total=0
    by_source={r:[] for r in range(D.controls)}
    for i,e in enumerate(D.edges):by_source[e.source].append((i,e))
    for inds in product(range(len(actions)),repeat=h):
        if max_tuples is not None and checked>=max_tuples:
            return dict(status='UNKNOWN',reason='action-tuple cap',exhausted=False,
                        actions=len(actions),tuples_checked=checked)
        checked+=1;tails=[None]*h;rest=J.identity
        for j in reversed(range(h)):
            rest=compose(compose(J.letters[D.marker(j)],actions[inds[j]]),rest);tails[j]=rest
        if not J.accepting(mi,tails[0][J.start(mi)]):continue
        allowed=[J.accepting(i,tails[e.kind][J.start(i)]) for i,e in enumerate(D.edges)]
        unit_actions=[compose(t,J.letters[D.end]) for t in tails]
        ending=compose(J.letters[D.switch],unit_actions[0])
        initial=(D.start,J.start(oi));todo=deque([initial]);parent={initial:None};graphs+=1
        found=None
        while todo:
            r,q=todo.popleft();nodes_total+=1
            if r in D.finals and J.accepting(oi,ending[q]):found=(r,q);break
            for i,e in by_source[r]:
                if not allowed[i]:continue
                qq=unit_actions[e.kind][q]
                if qq==J.sink:continue
                nxt=(e.target,qq)
                if nxt not in parent:parent[nxt]=((r,q),e.kind);todo.append(nxt)
        if found is not None:
            seq=[];node=found
            while parent[node] is not None:
                node,j=parent[node];seq.append(j)
            seq.reverse();data=tuple(reps[x] for x in inds);w=materialize(D,data,seq)
            # Independent token parser checks the semantic family and all guards.
            if not semantic_witness(D,w):raise AssertionError('Invalid reconstructed solution')
            return dict(status='YES',exhausted=False,data=data,sequence=seq,word=w,
                        actions=len(actions),tuples_checked=checked,graphs=graphs,
                        graph_nodes=nodes_total,joint_states=J.n,
                        representative_length_bound=len(actions)-1,
                        unit_count_bound=D.controls*D.output_guard.n-1)
    return dict(status='NO',exhausted=True,actions=len(actions),tuples_checked=checked,
                graphs=graphs,graph_nodes=nodes_total,joint_states=J.n,
                theoretical_tuples=len(actions)**h)


def two_reference_example() -> Description:
    """Requires both noncommuting references and returns through a common hub."""
    h=2;a=h+4;U=universal(a)
    # Control language: (0|1)* 0 1, represented without nondeterminism.
    # Every word ending in 0,1 is admitted; arbitrary earlier alternation remains.
    es=(Edge(0,0,1,U),Edge(0,1,0,U),Edge(1,0,1,U),Edge(1,1,2,U),
        Edge(2,0,1,U),Edge(2,1,0,U))
    master=finite_language(((2,0,3,1),),a)
    return Description(h,3,0,frozenset({2}),es,master,U)


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--demo',action='store_true')
    p.add_argument('--output');args=p.parse_args()
    if not args.demo:p.error('Choose --demo')
    D=two_reference_example();out=solve(D);I=compile_tokens(D);B,c=compile_binary(I)
    if out['status']=='YES':
        w=tuple(out['word']);bits=encode(w,c)
        assert witness_direct(I,w) and witness_reverse(I,w)
        assert witness_direct(B,bits) and witness_reverse(B,bits)
        out['binary_witness']=''.join(map(str,bits))
    out.update(token_states=I.machine.n,binary_states=B.machine.n,flags=len(B.flags),
               description=D.as_json(),scope='Supplied shared-suffix switching description only')
    text=json.dumps(out,indent=2,sort_keys=True)+'\n'
    if args.output:
        from pathlib import Path
        Path(args.output).write_text(text,encoding='utf-8')
    print(text)

if __name__=='__main__':main()
