"""Independent normalized top-free bridge, with bottom denials.

Integer variables 0..k-1. Constraints are ('lower',left,right,target),
('upper',source,left,right), ('leq',source,target), ('denial',source).
All saturation and regular-language checks are exact, not depth-bounded.
"""
from collections import deque
from dataclasses import dataclass
from border_lab import Instance

class NFA:
    def __init__(self,n):
        self.eps=[{i} for i in range(n)]
        self.edges=[[set(),set()] for _ in range(n)]
    def node(self):
        i=len(self.eps); self.eps.append({i}); self.edges.append([set(),set()]); return i
    def close(self):
        changed=True
        while changed:
            changed=False
            for p in range(len(self.eps)):
                z=set().union(*(self.eps[q] for q in self.eps[p]))
                if not z<=self.eps[p]: self.eps[p].update(z); changed=True
    def saturate(self,rules):
        for p,q,op,a in rules:
            if op=='eps': self.eps[p].add(q)
            if op=='pop': self.edges[p][a].add(q)
        while True:
            self.close(); before=tuple(map(frozenset,self.eps))
            for p,q,op,a in rules:
                if op=='push':
                    for r in tuple(self.eps[q]):
                        for s in self.edges[r][a]: self.eps[p].update(self.eps[s])
            if before==tuple(map(frozenset,self.eps)): break
    def step(self,subset,a):
        return frozenset(s for p in subset for q in self.edges[p][a] for s in self.eps[q])
    def run(self,start,word):
        current=frozenset(self.eps[start])
        for a in word: current=self.step(current,int(a))
        return current

def normalize(k,constraints):
    rules=[]; forced=set(); denials=set()
    for c in constraints:
        if any(not isinstance(q,int) or not 0<=q<k for q in c[1:]): raise ValueError(c)
        if c[0]=='lower':
            _,p,q,r=c; rules.extend(((p,r,'push',0),(q,r,'push',1))); forced.add(r)
        elif c[0]=='upper':
            _,p,q,r=c; rules.extend(((p,q,'pop',0),(p,r,'pop',1)))
        elif c[0]=='leq':
            _,p,q=c; rules.append((p,q,'eps',-1))
        elif c[0]=='denial': denials.add(c[1])
        else: raise ValueError(c)
    return tuple(rules),frozenset(forced),frozenset(denials)

def reverse(rules):
    return tuple((q,p,{'eps':'eps','push':'pop','pop':'push'}[op],a) for p,q,op,a in rules)

@dataclass
class Bridge:
    instance: Instance
    classes: tuple
    forced: frozenset
    denials: frozenset
    rules: tuple
    w: NFA
    a: NFA
    safety: NFA

def build(k,constraints,alpha=0,beta=1,max_classes=10000):
    rules,forced,denials=normalize(k,constraints)
    safety=NFA(k+1)
    for p in denials: safety.eps[p].add(k)
    for a in (0,1): safety.edges[k][a].add(k)
    safety.saturate(rules)
    if any(k in safety.eps[p] for p in forced): return 'UNSAT',None
    w=NFA(k); w.saturate(rules)
    a=NFA(k); a.saturate(reverse(rules))
    initial=(frozenset(w.eps[alpha]),frozenset(a.eps[beta]),frozenset(safety.eps[alpha]))
    classes=[initial]; ids={initial:0}; delta=[]
    for bsub,asub,ssub in classes:
        row=[]
        for letter in (0,1):
            nxt=(w.step(bsub,letter),a.step(asub,letter),safety.step(ssub,letter))
            if nxt not in ids:
                if len(classes)>=max_classes: return 'UNKNOWN',None
                ids[nxt]=len(classes); classes.append(nxt)
            row.append(ids[nxt])
        delta.append(tuple(row))
    final=frozenset(i for i,(_,x,_) in enumerate(classes) if not x&forced)
    bad=frozenset(i for i,(_,_,x) in enumerate(classes) if k in x)
    flags=frozenset((i,j) for i,(x,_,_) in enumerate(classes) for j,(_,y,_) in enumerate(classes) if x&y)
    inst=Instance(tuple(delta),final,flags,bad)
    return 'SAT',Bridge(inst,tuple(classes),forced,denials,rules,w,a,safety)

class Canonical:
    """Regular post-closure, checked independently of summary flags."""
    def __init__(self,k,constraints,alpha,beta,path):
        self.k=k; self.constraints=tuple(constraints); self.alpha=alpha; self.beta=beta; self.path=path
        rules,forced,_=normalize(k,constraints)
        self.nfa=NFA(k+1); self.final=k
        seeds=[(alpha,path[:j]) for j in range(len(path)+1)]+[(p,'') for p in forced]
        for p,word in seeds:
            if not word: self.nfa.eps[p].add(k); continue
            for j,a in enumerate(word):
                target=k if j==len(word)-1 else self.nfa.node()
                self.nfa.edges[p][int(a)].add(target); p=target
        self.nfa.saturate(reverse(rules))
    def start(self,p): return frozenset(self.nfa.eps[p])
    def contains(self,p,w): return self.final in self.nfa.run(p,w)
    def included(self,x,y):
        queue=deque([(x,y)]); seen={(x,y)}
        while queue:
            x,y=queue.popleft()
            if self.final in x and self.final not in y: return False
            for a in (0,1):
                pair=(self.nfa.step(x,a),self.nfa.step(y,a))
                if pair not in seen: seen.add(pair); queue.append(pair)
        return True
    def prefix_closed(self,p):
        start=self.start(p); todo=[(start,False)]; seen=set(todo)
        for x,missing in todo:
            here=self.final in x
            if here and missing: return False
            for a in (0,1):
                pair=(self.nfa.step(x,a),missing or not here)
                if pair not in seen: seen.add(pair); todo.append(pair)
        return True
    def errors(self):
        out=[]; step=self.nfa.step
        for c in self.constraints:
            if c[0]=='lower':
                _,p,q,r=c
                if not self.contains(r,'') or not self.included(self.start(p),step(self.start(r),0)) or not self.included(self.start(q),step(self.start(r),1)): out.append(c)
            elif c[0]=='upper':
                _,p,q,r=c
                if not self.included(step(self.start(p),0),self.start(q)) or not self.included(step(self.start(p),1),self.start(r)): out.append(c)
            elif c[0]=='leq':
                _,p,q=c
                if not self.included(self.start(p),self.start(q)): out.append(c)
            elif c[0]=='denial':
                if not self.included(self.start(c[1]),frozenset()): out.append(c)
        if not all(self.prefix_closed(p) for p in range(self.k)): out.append('not prefix-closed')
        if not self.contains(self.alpha,self.path): out.append('missing alpha seed')
        if self.contains(self.beta,self.path): out.append('beta contains path')
        return out


def reduced(bridge,alpha=0,beta=1,max_classes=10000):
    """Remove the third safety component, retaining every-prefix Bad checks.

    Valid only for a satisfiable normalized system. See safety-elimination proof.
    """
    w,a=bridge.w,bridge.a
    first=(frozenset(w.eps[alpha]),frozenset(a.eps[beta]))
    classes=[first]; ids={first:0}; delta=[]
    for bsub,asub in classes:
        row=[]
        for letter in (0,1):
            nxt=(w.step(bsub,letter),a.step(asub,letter))
            if nxt not in ids:
                if len(classes)>=max_classes: return None,None
                ids[nxt]=len(classes); classes.append(nxt)
            row.append(ids[nxt])
        delta.append(tuple(row))
    final=frozenset(i for i,(_,x) in enumerate(classes) if not x&bridge.forced)
    bad=frozenset(i for i,(x,_) in enumerate(classes) if x&bridge.denials)
    flags=frozenset((i,j) for i,(x,_) in enumerate(classes) for j,(_,y) in enumerate(classes) if x&y)
    return Instance(tuple(delta),final,flags,bad),tuple(classes)
