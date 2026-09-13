#!/usr/bin/env python3
"""Exact target anchoring certificates; not an unrestricted decision algorithm.

A finite certificate reduces some sparse instances to complete target columns.
A native terminating algorithm decides that class and reconstructs a witness
of length at most k*k+k-2. Uncertified cases stay UNKNOWN. No string-SMT or
external word-equation backend is needed. The one-not-contains compiler is
retained as an independently testable alternative formulation.
Python 3.10+, standard library only.
"""
from __future__ import annotations
from dataclasses import dataclass
from collections import deque
from itertools import product
import argparse, json
from pathlib import Path

@dataclass(frozen=True)
class Instance:
    delta: tuple[tuple[int,...],...]
    start: int
    finals: frozenset[int]
    flags: frozenset[tuple[int,int]] = frozenset()
    bad: frozenset[int] = frozenset()
    def __post_init__(self):
        k=len(self.delta)
        if not k or not 0<=self.start<k: raise ValueError('Invalid state set/start')
        a=len(self.delta[0])
        if not a or any(len(r)!=a for r in self.delta): raise ValueError('Invalid alphabet')
        if any(type(x)is not int or not -1<=x<k for r in self.delta for x in r): raise ValueError('Invalid transition')
        if any(not 0<=q<k for q in self.finals|self.bad): raise ValueError('Invalid state annotation')
        if any(not (0<=p<k and 0<=t<k) for p,t in self.flags): raise ValueError('Invalid flag')
        if any(any(x!=-1 for x in self.delta[f]) for f in self.finals): raise ValueError('Finals must be terminal')
    @property
    def k(self): return len(self.delta)
    @property
    def alphabet(self): return len(self.delta[0])
    def run(self,w):
        q=self.start;c=[q]
        for a in w:
            if type(a)is not int or not 0<=a<self.alphabet: raise ValueError('Invalid input symbol')
            q=self.delta[q][a]
            if q<0:return None
            c.append(q)
        return tuple(c)
    def accepted(self,w):
        c=self.run(w)
        return c is not None and c[-1]in self.finals and not self.bad.intersection(c)
    def as_json(self):
        return dict(delta=self.delta,start=self.start,finals=sorted(self.finals),flags=sorted(self.flags),bad=sorted(self.bad))

def witness(I,w):
    c=I.run(w)
    if c is None or c[-1]not in I.finals or I.bad.intersection(c):return False
    return all((c[i],c[j])not in I.flags or w[i:i+len(w)-j]!=w[j:]
               for i in range(len(c)) for j in range(i,len(c)))

def reverse_witness(I,w):
    c=I.run(w)
    if c is None or c[-1]not in I.finals or I.bad.intersection(c):return False
    r=w[::-1];q=c[::-1]
    for n in range(len(r)+1):
        for b in range(n+1):
            if (q[n],q[b])in I.flags and r[:b]==r[n-b:n]:return False
    return True

def reach(adj,starts):
    seen=set(starts); todo=list(seen)
    for p in todo:
        for q in adj.get(p,()):
            if q not in seen:seen.add(q);todo.append(q)
    return seen

def normalize(I,f):
    if f not in I.finals:raise ValueError('Not a final')
    removed=I.bad|{p for p,t in I.flags if p==t or t==f}
    allowed=set(range(I.k))-removed
    if I.start not in allowed or f not in allowed:return None
    adj={p:{q for q in I.delta[p] if q in allowed} for p in allowed}
    rev={p:set() for p in allowed}
    for p,qs in adj.items():
        for q in qs:rev[q].add(p)
    live=reach(adj,[I.start])&reach(rev,[f])
    if I.start not in live:return None
    order=tuple(sorted(live));ids={p:i for i,p in enumerate(order)}
    rows=tuple(tuple(ids.get(q,-1) for q in I.delta[p]) for p in order)
    flags=frozenset((ids[p],ids[t]) for p,t in I.flags if p in live and t in live and p!=f and t!=f and p!=t)
    return Instance(rows,ids[I.start],frozenset({ids[f]}),flags),order

def pair_graph(I,avoid_flags):
    f=next(iter(I.finals));nodes=[(p,t) for p in range(I.k) for t in range(I.k) if p!=t and p!=f]
    edges={v:[] for v in nodes}
    for p,t in nodes:
        for a in range(I.alphabet):
            q,u=I.delta[p][a],I.delta[t][a]
            if min(q,u)<0 or q==u or q==f:continue
            if avoid_flags and (q,u)in I.flags:continue
            edges[p,t].append(((q,u),a))
    return edges,{(p,f) for p in range(I.k) if p!=f}

def color_certificate(I):
    """I must be a trimmed boundary-safe single-final slice."""
    if len(I.finals)!=1 or I.bad or any(p==t or p in I.finals or t in I.finals for p,t in I.flags):
        raise ValueError('Boundary-normalized single-final slice required')
    defined=[(p,a) for p in range(I.k) for a,q in enumerate(I.delta[p]) if q>=0]
    parent={e:e for e in defined}
    def find(x):
        while parent[x]!=x:parent[x]=parent[parent[x]];x=parent[x]
        return x
    def union(x,y):
        x,y=find(x),find(y)
        if x!=y:parent[max(x,y)]=min(x,y)
    pairs,ends=pair_graph(I,True)
    adj={v:[u for u,a in es] for v,es in pairs.items()};rev={v:[] for v in pairs}
    for v,es in pairs.items():
        for u,a in es:rev[u].append(v)
    forward=reach(adj,I.flags);back=reach(rev,ends);productive=forward&back
    obligations=[]
    for p,t in sorted(productive):
        for (q,u),a in pairs[p,t]:
            if (q,u) in productive:
                union((p,a),(t,a));obligations.append((p,t,a,q,u))
    classes=sorted({find(e) for e in defined});ci={e:i for i,e in enumerate(classes)}
    colors={e:ci[find(e)] for e in defined}
    # Even an empty candidate word has a finite nonempty working alphabet.
    alphabet=max(1,len(classes));rows=[[-1]*alphabet for _ in range(I.k)]
    for (p,a),col in colors.items():
        if rows[p][col]!=-1:raise AssertionError('Coloring merged different outgoing letters')
        rows[p][col]=I.delta[p][a]
    colored=Instance(tuple(map(tuple,rows)),I.start,I.finals,I.flags)
    targets={t for p,t in I.flags}
    pg,ends=pair_graph(colored,True)
    root_order={p:reach({s:[q for q in row if q>=0] for s,row in enumerate(I.delta)},[p]) for p in range(I.k)}
    # Search for a target match whose entire aligned pair path misses G.
    roots=[(p,t) for t in sorted(targets) for p in range(I.k)
           if p!=t and p not in I.finals and (p,t)not in I.flags and t in root_order[p]]
    queue=deque(roots);pred={v:None for v in roots};found=None
    while queue:
        v=queue.popleft()
        if v in ends:found=v;break
        for u,a in pg[v]:
            if u not in pred:pred[u]=(v,a);queue.append(u)
    obstruction=None
    if found is not None:
        v=found;letters=[];path=[v]
        while pred[v]is not None:v,a=pred[v];letters.append(a);path.append(v)
        obstruction=dict(root=v,letters=list(reversed(letters)),pairs=list(reversed(path)),
                         meaning='Synchronized-path obstruction only; not a NO result or necessarily a realized comparison')
    full=frozenset((p,t) for t in targets for p in range(I.k) if p!=t and p not in I.finals)
    J=Instance(colored.delta,colored.start,colored.finals,full)
    return dict(status='CERTIFIED' if obstruction is None else 'UNKNOWN',instance=J,
                colored_original=colored,colors=colors,classes=classes,
                obligations=obligations,targets=targets,obstruction=obstruction)

def encode(I,w,cert):
    c=I.run(w)
    if c is None:raise ValueError('Defined original run required')
    return tuple(cert['colors'][p,a] for p,a in zip(c,w))

def anchored_word_test(J,w):
    if not J.accepted(w):return False
    c=J.run(w);T={t for p,t in J.flags}
    positions=[i for i,t in enumerate(c) if t in T]
    if not positions:return True
    j=positions[-1];Y=w[j:]
    return all(w[i:i+len(Y)]!=Y for i in range(j))

def dfa_json(rows,start,finals):return dict(delta=rows,start=start,finals=sorted(finals))

def compile_anchor(J):
    """Finite disjunction of NC(XZ,Za) with regular X,Z, plus target-free branch."""
    T={t for p,t in J.flags};f=next(iter(J.finals))
    expected={(p,t) for p in range(J.k) for t in T if p!=t and p!=f}
    if J.bad or len(J.finals)!=1 or J.flags!=expected:raise ValueError('Complete target columns required')
    free=tuple(tuple(q if q not in T else -1 for q in row) for row in J.delta)
    target_free=dfa_json(free,J.start, {f} if J.start not in T else set())
    branches=[]
    # The fresh start allows the chosen last target once. All subsequent T cuts reject.
    for t in sorted(T):
        rows=[list(row) for row in J.delta]+[list(J.delta[t])]
        for row in rows:
            for a,q in enumerate(row):
                if q in T:row[a]=-1
        fresh=J.k
        for a in range(J.alphabet):
            # Za reaches f, with no T after the initial t. q may be fresh for Z=epsilon.
            accepting={q for q in range(J.k) if q not in T and J.delta[q][a]==f}
            if J.delta[t][a]==f:accepting.add(fresh)
            if not accepting:continue
            branches.append(dict(target=t,last_letter=a,
                 X=dfa_json(J.delta,J.start,{t}),
                 Z=dfa_json(tuple(map(tuple,rows)),fresh,accepting),
                 not_contains=dict(haystack=['X','Z'],needle=['Z',{'letter':a}]),
                 output=['X','Z',{'letter':a}]))
    return dict(alphabet_size=J.alphabet,target_free=target_free,branches=branches,
                external_theorem='Havlena--Hecko--Holik--Lengal, MFCS 2025, Theorem 28',
                backend='Alternative formula only; solve_columns implements a separate complete native algorithm')

def dfa_accepts(d,w):
    q=d['start']
    for a in w:
        q=d['delta'][q][a]
        if q<0:return False
    return q in d['finals']

def compiled_word_test(formula,w):
    if dfa_accepts(formula['target_free'],w):return True
    for b in formula['branches']:
        a=b['last_letter']
        if not w or w[-1]!=a:continue
        for i in range(len(w)):
            X,Z=w[:i],w[i:-1]
            if not (dfa_accepts(b['X'],X) and dfa_accepts(b['Z'],Z)):continue
            needle=Z+(a,);haystack=X+Z
            if all(haystack[j:j+len(needle)]!=needle for j in range(len(haystack)-len(needle)+1)):return True
    return False

# Reference fixtures from prior notes; their global classifications are not inferred by a cutoff.
FIXTURES={
 'marking_barrier':Instance(((1,2),(1,2),(3,-1),(3,4),(5,2),(-1,-1)),0,frozenset({5}),frozenset({(0,2),(0,3),(1,2)})),
 'nonflat_target':Instance(((1,0),(0,2),(-1,-1)),0,frozenset({2}),frozenset({(0,1)})),
 'exceptional_conjugacy':Instance(((1,3),(-1,2),(0,-1),(4,-1),(-1,5),(-1,-1)),0,frozenset({5}),frozenset({(0,2)})),
}

# Complete native decision for the anchored class. No string-SMT engine.
def shortest_path(I,start,finals,forbidden=frozenset(),minimum=0):
    """All subsequent cut states must avoid forbidden; the initial cut is exempt."""
    initial=(start,0);todo=deque([initial]);parent={initial:None}
    while todo:
        q,depth=todo.popleft()
        if q in finals and depth>=minimum:
            node=(q,depth);word=[]
            while parent[node]is not None:node,a=parent[node];word.append(a)
            return tuple(reversed(word))
        for a,r in enumerate(I.delta[q]):
            if r<0 or r in forbidden:continue
            node=(r,min(minimum,depth+1))
            if node not in parent:parent[node]=((q,depth),a);todo.append(node)
    return None

def tail_analysis(J,t,T, *, enumerate_words=True):
    """Return all finite tail words, or an actual productive-cycle indication."""
    # Keep t as initial only: no edge can re-enter any target.
    adj={p:{q for q in J.delta[p] if q>=0 and q not in T} for p in range(J.k)}
    forward=reach(adj,[t]);rev={p:set() for p in range(J.k)}
    for p,qs in adj.items():
        for q in qs:rev[q].add(p)
    useful=forward&reach(rev,J.finals)
    if t not in useful:return dict(infinite=False,words=[],useful=[])
    indeg={p:0 for p in useful}
    for p in useful:
        for q in adj[p]&useful:indeg[q]+=1
    todo=deque(p for p in useful if indeg[p]==0);order=[]
    while todo:
        p=todo.popleft();order.append(p)
        for q in adj[p]&useful:
            indeg[q]-=1
            if indeg[q]==0:todo.append(q)
    if len(order)<len(useful):return dict(infinite=True,useful=sorted(useful))
    if not enumerate_words:return dict(infinite=False,useful=sorted(useful))
    words=[];todo=[(t,())]
    while todo:
        p,w=todo.pop()
        if p in J.finals:words.append(w)
        for a,q in enumerate(J.delta[p]):
            if q in useful and q not in T:todo.append((q,w+(a,)))
    if any(len(w)>=J.k for w in words):raise AssertionError('Finite target-free tail exceeded acyclic bound')
    return dict(infinite=False,words=sorted(words),useful=sorted(useful))

def kmp_avoid(pattern,alphabet):
    if not pattern:raise ValueError('Nonempty needle required')
    L=len(pattern);pi=[0]*L
    for i in range(1,L):
        j=pi[i-1]
        while j and pattern[i]!=pattern[j]:j=pi[j-1]
        if pattern[i]==pattern[j]:j+=1
        pi[i]=j
    rows=[]
    for q in range(L):
        row=[]
        for a in range(alphabet):
            j=q
            while j and pattern[j]!=a:j=pi[j-1]
            if pattern[j]==a:j+=1
            row.append(j if j<L else -1)
        rows.append(tuple(row))
    return tuple(rows)

def avoid_prefix(J,t,Y, *, certificate=False):
    """Shortest X reaching t with Y absent from X Y[:-1]; graph exhaustion is exact."""
    K=kmp_avoid(Y,J.alphabet);finalK=set()
    for q in range(len(Y)):
        r=q
        for a in Y[:-1]:
            r=K[r][a]
            if r<0:break
        if r>=0:finalK.add(q)
    initial=(J.start,0);todo=deque([initial]);parent={initial:None}
    while todo:
        p,q=todo.popleft()
        if p==t and q in finalK:
            w=[];node=(p,q)
            while parent[node]is not None:node,a=parent[node];w.append(a)
            return tuple(reversed(w)),len(parent),None
        for a,r in enumerate(J.delta[p]):
            s=K[q][a]
            if min(r,s)<0:continue
            node=(r,s)
            if node not in parent:parent[node]=((p,q),a);todo.append(node)
    return None,len(parent),(dict(target=t,tail=Y,reachable=sorted(parent)) if certificate else None)

def solve_columns(J):
    """Complete YES/NO for trimmed boundary-safe complete-target-column instances."""
    T={t for p,t in J.flags};f=next(iter(J.finals))
    expected={(p,t) for t in T for p in range(J.k) if p!=t and p!=f}
    if len(J.finals)!=1 or J.bad or set(J.flags)!=expected:raise ValueError('Wrong anchored class')
    stats=dict(tail_words=0,avoidance_states=0,infinite_tail=None); proofs=[]
    def yes(w,reason):
        if not witness(J,w) or not reverse_witness(J,w):raise AssertionError('Invalid reconstructed anchored witness')
        bound=0 if J.k==1 else J.k*J.k+J.k-2
        if len(w)>bound:raise AssertionError('Witness exceeds proved bound')
        return dict(status='YES',word=w,reason=reason,bound=bound,**stats)
    if J.start not in T:
        w=shortest_path(J,J.start,J.finals,T)
        if w is not None:return yes(w,'target-free path')
    for t in sorted(T):
        info=tail_analysis(J,t,T)
        if info['infinite']:
            X=shortest_path(J,J.start,{t})
            if X is None:raise AssertionError('Slice not trimmed')
            m=len(X);stats['infinite_tail']=t
            Y=shortest_path(J,t,J.finals,T,minimum=J.k*m)
            if Y is None:raise AssertionError('Infinite productive tail had no long word')
            if len(Y)>J.k*m+J.k-1:raise AssertionError('Long-tail upper bound failed')
            return yes(X+Y,'productive target-free tail cycle; terminal period bound')
        for Y in info['words']:
            stats['tail_words']+=1
            X,states,proof=avoid_prefix(J,t,Y,certificate=True);stats['avoidance_states']+=states
            if proof is not None:proofs.append(proof)
            if X is not None:return yes(X+Y,'finite tail with exhaustive pattern-avoidance product')
    return dict(status='NO',reason='all last-target tails and their entire prefix languages exhausted',
                certificate=dict(prefix_exhaustions=proofs),**stats)

def solve(I):
    """Sound partial all-input solver. UNKNOWN when a nonempty slice lacks a certificate."""
    slices=[];unknown=False
    for f in sorted(I.finals):
        normalized=normalize(I,f)
        if normalized is None:slices.append(dict(final=f,status='NO',reason='empty boundary slice'));continue
        J,old=normalized
        cert=color_certificate(J)
        if cert['status']=='UNKNOWN':
            unknown=True;slices.append(dict(final=f,status='UNKNOWN',obstruction=cert['obstruction']));continue
        out=solve_columns(cert['instance']);slices.append(dict(final=f,**out))
        if out['status']=='YES':
            raw=tuple(cert['classes'][a][1] for a in out['word'])
            if not witness(I,raw) or not reverse_witness(I,raw):raise AssertionError('Invalid decoded original witness')
            return dict(status='YES',word=raw,slices=slices)
    return dict(status='UNKNOWN' if unknown else 'NO',slices=slices)


def generic_unique_tail(I):
    """A sound all-input YES test on a boundary-normalized, trimmed slice.

    This does NOT require complete columns or the color certificate. Target-free
    paths, or arbitrarily long target-free accepting tails after any target,
    supply actual witnesses for arbitrary flags. Absence of this condition is
    inconclusive; it is not an independent negative algorithm.
    """
    T={t for p,t in I.flags}
    if I.start not in T:
        w=shortest_path(I,I.start,I.finals,T)
        if w is not None:
            assert witness(I,w) and reverse_witness(I,w)
            return dict(status='YES',word=w,reason='target-free path')
    for t in sorted(T):
        info=tail_analysis(I,t,T,enumerate_words=False)
        if not info['infinite']:continue
        X=shortest_path(I,I.start,{t})
        if X is None:continue
        Y=shortest_path(I,t,I.finals,T,minimum=I.k*len(X))
        assert Y is not None
        w=X+Y
        assert witness(I,w) and reverse_witness(I,w)
        assert len(w)<=I.k*I.k+I.k-2
        return dict(status='YES',word=w,target=t,reason='productive target-free accepting tail')
    return dict(status='UNKNOWN',reason='No target-free path or productive last-target cycle')


def solve_with_tail_test(I):
    """Extra YES certificates first, then the exact certified-class solver."""
    for f in sorted(I.finals):
        norm=normalize(I,f)
        if norm is None:continue
        J,order=norm
        out=generic_unique_tail(J)
        if out['status']=='YES':
            assert witness(I,out['word']) and reverse_witness(I,out['word'])
            return dict(status='YES',word=out['word'],reason=out['reason'],final=f,
                        bound=0 if J.k==1 else J.k*J.k+J.k-2)
    return solve(I)


FIXTURES.update({
 'modular_positive_unknown':Instance(((-1,1),(-1,2),(3,1),(-1,4),(-1,5),(-1,6),(7,4),(-1,-1)),
    0,frozenset({7}),frozenset({(0,4),(0,5),(0,6),(1,3),(2,3)})),
 'sparse_cycle_yes':Instance(((3,6),(4,1),(7,2),(3,5),(7,2),(0,1),(-1,0),(-1,-1)),
    0,frozenset({7}),frozenset({(5,0),(5,6),(6,5)})),
 'recurrent_yes':Instance(((4,-1),(0,3),(1,3),(5,2),(0,1),(-1,-1)),0,frozenset({5}),
    frozenset({(0,1),(1,3),(2,0),(2,1),(2,3),(4,0),(4,1)})),
 'recurrent_no':Instance(((5,0),(0,6),(-1,0),(4,-1),(-1,2),(3,1),(-1,-1)),0,frozenset({6}),
    frozenset({(0,1),(0,4),(1,0),(1,5),(2,1),(2,3),(3,2),(3,4),(3,5),(4,1),(4,5),(5,1),(5,2)})),
})


def certificate_json(cert):
    return dict(status=cert['status'],targets=sorted(cert['targets']),
        colors=[dict(state=p,letter=a,color=c) for (p,a),c in sorted(cert['colors'].items())],
        classes=cert['classes'],obligations=cert['obligations'],
        obstruction=cert['obstruction'],completed_instance=cert['instance'].as_json(),
        colored_original=cert['colored_original'].as_json())


def from_json(d):
    return Instance(tuple(tuple(r) for r in d['delta']),d['start'],frozenset(d['finals']),
                    frozenset(tuple(x) for x in d.get('flags',[])),frozenset(d.get('bad',[])))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    source=parser.add_mutually_exclusive_group(required=True)
    source.add_argument('--fixture',choices=sorted(FIXTURES))
    source.add_argument('--input',type=Path,help='JSON Instance with delta/start/finals/flags/bad')
    parser.add_argument('--output',type=Path)
    parser.add_argument('--certificate-output',type=Path,help='Save finite color and column proofs')
    args=parser.parse_args()
    if not __debug__:parser.error('Run without Python -O; certificate assertions must execute')
    try:I=FIXTURES[args.fixture] if args.fixture else from_json(json.loads(args.input.read_text()))
    except (ValueError,KeyError,TypeError) as error:parser.error(str(error))
    result=solve_with_tail_test(I)
    result['scope']='Sound YES/NO; failed sufficient certificate remains UNKNOWN. Not an unrestricted decider.'
    if args.certificate_output:
        slices=[]
        for f in sorted(I.finals):
            norm=normalize(I,f)
            if norm is None:slices.append(dict(final=f,boundary_empty=True));continue
            J,old=norm;cert=color_certificate(J)
            entry=dict(final=f,original_states=old,normalized=J.as_json(),color=certificate_json(cert))
            if cert['status']=='CERTIFIED':entry['column_answer']=solve_columns(cert['instance'])
            slices.append(entry)
        args.certificate_output.write_text(json.dumps(dict(instance=I.as_json(),slices=slices),indent=2,sort_keys=True)+'\n')
    text=json.dumps(result,sort_keys=True,indent=2)+'\n'
    if args.output:args.output.write_text(text)
    print(text)

if __name__=='__main__':main()
