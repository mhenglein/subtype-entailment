#!/usr/bin/env python3
"""Finite counter lifts and exact word-equation compilation for supplied walks.

All variables range over finite binary words. The JSON output is an explicit
existential formula with finite DFA atoms; it is NOT a SAT/UNSAT solver.
The repeated-boundary macro is expanded from Subtail C071, at commit
52d5270342b27aee3cad10e1b2d0ac7d9307a580. Its mathematical proof is a dependency,
not claimed to have been independently formally verified by this module.
"""
from __future__ import annotations
from dataclasses import dataclass
from typing import Iterable, Optional
import argparse, json

@dataclass(frozen=True)
class Instance:
    delta: tuple[tuple[int, int], ...]
    start: int
    finals: frozenset[int]
    bad: frozenset[int]
    flags: frozenset[tuple[int, int]]

    def __post_init__(self):
        k = len(self.delta)
        if not k or not 0 <= self.start < k:
            raise ValueError('Invalid state set or initial state')
        if any(len(row) != 2 or any(t < -1 or t >= k for t in row) for row in self.delta):
            raise ValueError('Transitions must be binary and use -1 for undefined')
        if not (self.finals | self.bad) <= set(range(k)):
            raise ValueError('Invalid final/Bad state')
        if any(not (0 <= p < k and 0 <= q < k) for p,q in self.flags):
            raise ValueError('Invalid flag endpoint')
        if any(self.delta[f] != (-1,-1) for f in self.finals):
            raise ValueError('Final states must be terminal')

    @property
    def k(self): return len(self.delta)
    @property
    def sources(self): return frozenset(p for p,t in self.flags)

    def trace(self, word: str, start: Optional[int] = None):
        q = self.start if start is None else start
        if not 0 <= q < self.k or q in self.bad: return None
        ans = [q]
        for a in word:
            if a not in '01': raise ValueError('Words must be binary')
            q = self.delta[q][int(a)]
            if q < 0 or q in self.bad: return None
            ans.append(q)
        return ans

    def as_json(self):
        return dict(delta=self.delta,start=self.start,finals=sorted(self.finals),
                    bad=sorted(self.bad),flags=sorted(self.flags))

@dataclass(frozen=True)
class DFA:
    delta: tuple[tuple[int,int], ...]
    start: int
    finals: frozenset[int]
    def accepts(self, word: str):
        q = self.start
        for a in word:
            if a not in '01': raise ValueError('Words must be binary')
            q = self.delta[q][int(a)]
            if q < 0: return False
        return q in self.finals
    def as_json(self):
        return dict(alphabet=['0','1'],delta=self.delta,start=self.start,
                    finals=sorted(self.finals),undefined=-1)

NONEMPTY = DFA(((1,1),(1,1)),0,frozenset({1}))

def safe_table(I: Instance):
    return tuple(tuple(t if q not in I.bad and t >= 0 and t not in I.bad else -1
                       for t in row) for q,row in enumerate(I.delta))

def path_dfa(I: Instance, p: int, ends: Iterable[int]):
    return DFA(safe_table(I),p,frozenset(ends)-I.bad)

def first_return_dfa(I: Instance, p: int):
    tab = list(safe_table(I)); row = tab[p]; tab[p] = (-1,-1); tab.append(row)
    return DFA(tuple(tab),I.k,frozenset({p})-I.bad)

def no_capture_dfa(I: Instance, t: int):
    hit, miss = I.k, I.k+1
    tab=[]
    for q in range(I.k):
        if q in I.bad: tab.append((miss,miss)); continue
        if q in I.finals: tab.append((hit,hit)); continue
        row=[]
        for dest in I.delta[q]:
            row.append(miss if dest<0 or dest in I.bad else
                       hit if dest in I.finals else dest)
        tab.append(tuple(row))
    tab += [(hit,hit),(miss,miss)]
    start = miss if t in I.bad else hit if t in I.finals else t
    return DFA(tuple(tab),start,frozenset(range(I.k+2))-{hit})

def pair_monitor(I: Instance, p: int, s: int, forbidden: frozenset[int]):
    k=I.k
    def legal(a,b):
        return a not in I.bad and b not in I.bad and not (a==p and b in forbidden)
    tab=[]; finals=set()
    for a in range(k):
        for b in range(k):
            if not legal(a,b): tab.append((-1,-1)); continue
            finals.add(a*k+b); row=[]
            for x in (0,1):
                aa,bb=I.delta[a][x],I.delta[b][x]
                row.append(aa*k+bb if aa>=0 and bb>=0 and legal(aa,bb) else -1)
            tab.append(tuple(row))
    return DFA(tuple(tab),p*k+s,frozenset(finals))

def next_source_dfa(I: Instance, p: int, q: int):
    """Positive p-to-q path with no interior flagged source."""
    S=I.sources; tab=list(safe_table(I)); first=tab[p]
    for s in S: tab[s]=(-1,-1)
    def allowed(row): return tuple(t if t not in S or t==q else -1 for t in row)
    tab=[allowed(row) for row in tab]; tab.append(allowed(first))
    return DFA(tuple(tab),I.k,frozenset({q})-I.bad)

def entry_dfa(I: Instance, q: int):
    S=I.sources; tab=list(safe_table(I))
    for s in S: tab[s]=(-1,-1)
    for p,row in enumerate(tab):
        tab[p]=tuple(t if t not in S or t==q else -1 for t in row)
    return DFA(tuple(tab),I.start,frozenset({q})-I.bad)

def exit_dfa(I: Instance, p: int):
    tab=tuple(tuple(t if t not in I.sources else -1 for t in row)
              for row in safe_table(I))
    return DFA(tab,p,I.finals-I.bad)

def avoid_sources_dfa(I: Instance):
    S=I.sources; tab=list(safe_table(I))
    for p,row in enumerate(tab):
        tab[p]=(-1,-1) if p in S else tuple(t if t not in S else -1 for t in row)
    return DFA(tuple(tab),I.start,I.finals-I.bad-S)

def counter_lift(I: Instance, modulus: int, counted: Optional[frozenset[int]]=None):
    """Counter increments on arrival in counted; the initial position is excluded."""
    if not isinstance(modulus,int) or isinstance(modulus,bool) or modulus<1:
        raise ValueError('The modulus must be a positive integer')
    S=I.sources if counted is None else counted
    if not S <= set(range(I.k)): raise ValueError('Invalid counted set')
    d=modulus; tab=[]
    for q in range(I.k):
        for r in range(d):
            tab.append(tuple(-1 if t<0 else t*d+(r+int(t in S))%d for t in I.delta[q]))
    F=frozenset(f*d+r for f in I.finals for r in range(d))
    Bad=frozenset(q*d+r for q in I.bad for r in range(d))
    G=frozenset((p*d+r,t*d+s) for p,t in I.flags for r in range(d) for s in range(d))
    return Instance(tuple(tab),I.start*d,F,Bad,G)

def source_arrivals(I: Instance, word: str, start: int, counted=None):
    c=I.trace(word,start)
    if c is None: raise ValueError('The word must be a safe defined path')
    S=I.sources if counted is None else counted
    return sum(q in S for q in c[1:])

def guarded_power(I: Instance, p: int, B: str, U: str, counted=None):
    if not B: raise ValueError('The base must be nonempty')
    S=I.sources if counted is None else counted
    if p not in S: raise ValueError('The pivot must be counted')
    cb,cu=I.trace(B,p),I.trace(U,p)
    if cb is None or cu is None or cb[-1]!=p or cu[-1]!=p: return False
    d=sum(q in S for q in cb[1:])
    return U+B==B+U and sum(q in S for q in cu[1:])%d==0

def literal_power(B: str,U: str):
    if not B: raise ValueError('Empty base')
    return len(U)%len(B)==0 and B*(len(U)//len(B))==U

def witness_direct(I: Instance,w: str,start=None):
    c=I.trace(w,start)
    if c is None or c[-1] not in I.finals: return False
    return all((p,c[j]) not in I.flags or not w[i:].startswith(w[j:])
               for i,p in enumerate(c) for j in range(i,len(c)))

def witness_reversed(I: Instance,w: str,start=None):
    c=I.trace(w,start)
    if c is None or c[-1] not in I.finals:return False
    v=w[::-1];d=c[::-1]
    for b in range(len(v)+1):
        for ell in range(b+1):
            if (d[b],d[ell]) in I.flags and v[:ell]==v[b-ell:b]:return False
    return True

def boundary_good_direct(I: Instance,p: int,W: str,positions: Iterable[int]):
    c=I.trace(W,p)
    if c is None or c[-1] not in I.finals:return False
    return all((c[i],c[j]) not in I.flags or not W[i:].startswith(W[j:])
               for i in positions for j in range(i,len(c)))

def capture(I: Instance,t: int,W: str):
    if t in I.bad:return None
    q=t
    if q in I.finals:return ''
    for i,a in enumerate(W):
        q=I.delta[q][int(a)]
        if q<0 or q in I.bad:return None
        if q in I.finals:return W[:i+1]
    return None

def phi_value(I: Instance,p: int,t: int,W: str):
    c=I.trace(W,p)
    if c is None or c[-1] not in I.finals:raise ValueError('Phi needs an admissible word')
    V=capture(I,t,W)
    return V is None or not W.endswith(V) or c[len(W)-len(V)]!=t

def repeated_boundary_value(I: Instance,p: int,B: str,m: int,Y: str):
    """Concrete C071 algebra. It does not implement unbounded formula solving."""
    if m<0 or not first_return_dfa(I,p).accepts(B):raise ValueError('Invalid loop/exponent')
    cy=I.trace(Y,p)
    if cy is None or cy[-1] not in I.finals:raise ValueError('Tail must be admissible')
    T=frozenset(t for q,t in I.flags if q==p)
    W=B*m+Y
    if not all(phi_value(I,p,t,W) for t in T):return False
    for r in range(I.k):
        P=capture(I,r,Y)
        if not P or not Y.endswith(P):continue
        cut=len(Y)-len(P)
        if cy[cut]!=r:continue
        Q=Y[:cut];A=Q;ell=0
        while A.endswith(B):A=A[:-len(B)];ell+=1
        for j in range(min(m,ell)+1):
            trace=I.trace(A+B*(ell-j),p)
            assert trace is not None
            if trace[-1] in T:return False
        if m>ell and (B+A).endswith(B):
            D=(B+A)[:-len(B)];trace=I.trace(D,p)
            assert trace is not None
            if trace[-1] in T:return False
    return True

# Formula terms are lists of ["v", variable-name] or ["c", binary-constant].
Term=tuple[tuple[str,str], ...]
def var(name: str)->Term:return (('v',name),)
def const(s: str)->Term:
    if any(a not in '01' for a in s):raise ValueError('Nonbinary constant')
    return (('c',s),) if s else ()
def cat(*terms: Term)->Term:return tuple(a for t in terms for a in t)

def And(*xs):
    ys=[]
    for x in xs:
        if x['op']=='false':return {'op':'false'}
        if x['op']=='true':continue
        if x['op']=='and':ys.extend(x['args'])
        else:ys.append(x)
    return {'op':'true'} if not ys else ys[0] if len(ys)==1 else {'op':'and','args':ys}

def Or(*xs):
    ys=[]
    for x in xs:
        if x['op']=='true':return {'op':'true'}
        if x['op']=='false':continue
        if x['op']=='or':ys.extend(x['args'])
        else:ys.append(x)
    return {'op':'false'} if not ys else ys[0] if len(ys)==1 else {'op':'or','args':ys}

def Eq(x: Term,y: Term):return {'op':'eq','left':x,'right':y}

class FormulaBuilder:
    def __init__(self, ground=None):
        self.variables=set();self.serial=0;self.languages={};self.lang_ids={}
        self.ground = ground is not None
        self.values = dict(ground or {})
    def value(self,T):
        if not self.ground:return None
        out=[]
        for kind,x in T:
            if kind=='c':out.append(x)
            elif x in self.values:out.append(self.values[x])
            else:return None
        return ''.join(out)
    def assign(self,T,value):
        if self.ground and value is not None and len(T)==1 and T[0][0]=='v':
            self.values.setdefault(T[0][1],value)
    def named(self,name):self.variables.add(name);return var(name)
    def fresh(self,hint='x'):
        self.serial+=1;return self.named(f'{hint}_{self.serial}')
    def reg(self,t: Term,L: DFA):
        if L not in self.lang_ids:
            name=f'L{len(self.lang_ids):05d}';self.lang_ids[L]=name;self.languages[name]=L
        name=self.lang_ids[L]
        if len(t)==1 and t[0][0]=='v':
            return {'op':'reg','term':t,'language':name}
        z=self.fresh('regterm');self.assign(z,self.value(t))
        return And(Eq(z,t),{'op':'reg','term':z,'language':name})
    def ns(self,V: Term,W: Term):
        vv,ww=self.value(V),self.value(W)
        r=self.fresh('longer')
        if vv is not None and ww is not None and len(vv)>len(ww) and vv.endswith(ww):
            self.assign(r,vv[:len(vv)-len(ww)])
        branches=[And(Eq(V,cat(r,W)),self.reg(r,NONEMPTY))]
        for a,b in (('0','1'),('1','0')):
            r,t,z=(self.fresh('mismatch') for _ in range(3))
            if vv is not None and ww is not None:
                h=0
                while h<min(len(vv),len(ww)) and vv[-h-1]==ww[-h-1]:h+=1
                if h<len(vv) and h<len(ww) and vv[-h-1]==a and ww[-h-1]==b:
                    self.assign(r,vv[:len(vv)-h-1]);self.assign(t,ww[:len(ww)-h-1])
                    self.assign(z,vv[len(vv)-h:])
            branches.append(And(Eq(V,cat(r,const(a),z)),Eq(W,cat(t,const(b),z))))
        return Or(*branches)
    def phi(self,I,p,t,W):
        V,X,U=(self.fresh('capture') for _ in range(3))
        ww=self.value(W)
        if ww is not None:
            v=capture(I,t,ww)
            if v is not None:
                self.assign(V,v);self.assign(X,ww[len(v):])
                if ww.endswith(v):self.assign(U,ww[:len(ww)-len(v)])
        return Or(self.reg(W,no_capture_dfa(I,t)),
                  And(Eq(W,cat(V,X)),self.reg(V,path_dfa(I,t,I.finals)),
                      Or(self.ns(V,W),And(Eq(W,cat(U,V)),
                         self.reg(U,path_dfa(I,p,set(range(I.k))-{t}))))))
    def guard(self,I,p,T,Z,K):
        return Or(*(And(self.reg(Z,path_dfa(I,p,{s})),
                        self.reg(K,pair_monitor(I,p,s,T))) for s in range(I.k)))
    def power_test(self,I,p,T,B,U,Q):
        A,K,J1,J2,D=(self.fresh('conj') for _ in range(5))
        bb,uu,qq=self.value(B),self.value(U),self.value(Q)
        if bb and uu is not None and qq is not None:
            aa=qq
            while aa.endswith(bb):aa=aa[:-len(bb)]
            kk=qq[len(aa):];self.assign(A,aa);self.assign(K,kk)
            if kk.endswith(uu):self.assign(J1,kk[:len(kk)-len(uu)])
            if uu.startswith(kk):self.assign(J2,uu[len(kk):])
            if (bb+aa).endswith(bb):self.assign(D,(bb+aa)[:-len(bb)])
        return And(Eq(Q,cat(A,K)),Eq(cat(K,B),cat(B,K)),
                   self.reg(K,path_dfa(I,p,{p})),self.ns(B,A),
                   Or(And(Eq(K,cat(J1,U)),self.guard(I,p,T,cat(A,J1),U)),
                      And(Eq(U,cat(K,J2)),self.reg(J2,NONEMPTY),
                          self.guard(I,p,T,A,K),
                          Or(self.ns(B,cat(B,A)),
                             And(Eq(cat(B,A),cat(D,B)),
                                 self.reg(D,path_dfa(I,p,set(range(I.k))-T)))))))
    def boundaries(self,I,p,B,U,Y):
        T=frozenset(t for q,t in I.flags if q==p)
        clauses=[self.reg(B,first_return_dfa(I,p)),Eq(cat(U,B),cat(B,U)),
                 self.reg(U,path_dfa(I,p,{p})),self.reg(Y,path_dfa(I,p,I.finals))]
        if not T:return And(*clauses)
        clauses.extend(self.phi(I,p,t,cat(U,Y)) for t in sorted(T))
        for r in range(I.k):
            P,X,Q=(self.fresh('tailcap') for _ in range(3))
            yy=self.value(Y)
            if yy is not None:
                pp=capture(I,r,yy)
                if pp is not None:
                    self.assign(P,pp);self.assign(X,yy[len(pp):])
                    if yy.endswith(pp):self.assign(Q,yy[:len(yy)-len(pp)])
            clauses.append(Or(self.reg(Y,no_capture_dfa(I,r)),
               And(Eq(Y,cat(P,X)),self.reg(P,path_dfa(I,r,I.finals)),
                   Or(Eq(P,()),self.ns(P,Y),
                      And(Eq(Y,cat(Q,P)),
                          Or(self.reg(Q,path_dfa(I,p,set(range(I.k))-{r})),
                             self.power_test(I,p,T,B,U,Q)))))))
        return And(*clauses)
    def finish(self,formula,metadata):
        result={'format':'binary-existential-word-equations-with-dfa-atoms-v1',
                'quantifier':'exists','variables':sorted(self.variables),
                'variable_domain':'{0,1}*','languages':{n:L.as_json() for n,L in self.languages.items()},
                'formula':formula,'metadata':metadata}
        if self.ground:
            result['grounded_model']={v:self.values.get(v,'') for v in sorted(self.variables)}
            result['metadata']['grounded_model_note']='Constructed for supplied primary words, not an unbounded solver result'
        return result

@dataclass(frozen=True)
class Phase:
    pivot: int
    walk: Optional[tuple[int,...]]=None


def compile_scheme(I: Instance,phases: tuple[Phase,...],ground=None):
    """Compile supplied closed source walks, allowing repeated source labels.

    Each walk lists the source positions of ONE base, excluding its returning
    endpoint. Every adjacent pair (including the last-to-first pair) is joined
    by a positive path with source-free interior. Different bases and all tails
    retain common word variables across every clause.
    """
    f=FormulaBuilder(ground);W=f.named('W');S=I.sources
    for phase in phases:
        if phase.pivot not in S:raise ValueError('Every pivot must be a source')
        if phase.walk is not None and (not phase.walk or phase.walk[0]!=phase.pivot or
                                      any(s not in S for s in phase.walk)):
            raise ValueError('Invalid closed source-walk list')
    if not phases:
        return f.finish(f.reg(W,avoid_sources_dfa(I)),{'solver_executed':False,'phases':[]})
    h=len(phases);C=[f.named(f'C{i}') for i in range(h+1)]
    U=[f.named(f'U{i}') for i in range(h)]
    Y=[f.named(f'Y{i}') for i in range(h)]
    body=[]
    for i in range(h):body += [C[i],U[i]]
    body.append(C[h]);f.assign(W,f.value(cat(*body)))
    clauses=[Eq(W,cat(*body)),f.reg(C[0],entry_dfa(I,phases[0].pivot)),
             f.reg(C[h],exit_dfa(I,phases[-1].pivot))]
    for i in range(1,h):
        clauses.append(f.reg(C[i],next_source_dfa(I,phases[i-1].pivot,phases[i].pivot)))
    lift_sizes=[]
    for i,phase in enumerate(phases):
        tail=[C[i+1]]
        for j in range(i+1,h):tail += [U[j],C[j+1]]
        f.assign(Y[i],f.value(cat(*tail)))
        clauses.append(Eq(Y[i],cat(*tail)))
        clauses.append(f.reg(Y[i],path_dfa(I,phase.pivot,I.finals)))
        clauses.extend(f.phi(I,phase.pivot,t,Y[i]) for p,t in sorted(I.flags) if p==phase.pivot)
        if phase.walk is None:
            clauses.append(Eq(U[i],()));continue
        walk=phase.walk;d=len(walk);J=counter_lift(I,d);lift_sizes.append(J.k)
        A=[f.named(f'A{i}_{j}') for j in range(d)];B=f.named(f'B{i}')
        f.assign(B,f.value(cat(*A)))
        active=[f.reg(U[i],NONEMPTY),Eq(B,cat(*A)),Eq(cat(U[i],B),cat(B,U[i])),
                f.reg(U[i],path_dfa(J,phase.pivot*d,{phase.pivot*d}))]
        for j,p in enumerate(walk):
            active.append(f.reg(A[j],next_source_dfa(I,p,walk[(j+1)%d])))
        for j,p in enumerate(walk):
            P=cat(*A[:j]);Q=cat(*A[j:]);R=cat(Q,P);V=f.fresh('rotpower')
            pp,qq,uu=f.value(P),f.value(Q),f.value(U[i])
            if pp is not None and qq is not None and uu is not None and len(uu)>=len(pp)+len(qq):
                if uu.startswith(pp) and uu.endswith(qq):f.assign(V,uu[len(pp):len(uu)-len(qq)])
            active += [Eq(U[i],cat(P,V,Q)),f.boundaries(J,p*d,R,V,cat(Q,Y[i]))]
        # Base constraints occur only in this active branch. The empty-star
        # branch remains available when the prescribed base language is empty.
        clauses.append(Or(Eq(U[i],()),And(*active)))
    metadata={'solver_executed':False,
        'scope':'Exact formula for a supplied finite closed-source-walk power scheme; no cover theorem',
        'base_commit':'52d5270342b27aee3cad10e1b2d0ac7d9307a580',
        'dependency':'Subtail C071 repeated-boundary formula; written-proof status retained',
        'instance':I.as_json(),'phases':[{'pivot':p.pivot,'walk':p.walk} for p in phases],
        'local_lift_state_counts':lift_sizes,
        'note':'Each phase has its own counter; common word variables are NOT duplicated.'}
    return f.finish(And(*clauses),metadata)


def validate_formula(bundle):
    vars_=set(bundle['variables']);langs=bundle['languages'];stats={'nodes':0,'equations':0,'regular_atoms':0}
    def term(T):
        for kind,value in T:
            if kind=='v':assert value in vars_
            elif kind=='c':assert set(value)<=set('01')
            else:raise AssertionError('Unknown term atom')
    def visit(x):
        stats['nodes']+=1;op=x['op']
        if op in ('and','or'):
            for y in x['args']:visit(y)
        elif op=='eq':stats['equations']+=1;term(x['left']);term(x['right'])
        elif op=='reg':stats['regular_atoms']+=1;term(x['term']);assert x['language'] in langs
        else:assert op in ('true','false')
    visit(bundle['formula'])
    for L in langs.values():
        n=len(L['delta']);assert 0<=L['start']<n and set(L['finals'])<=set(range(n))
        assert all(len(r)==2 and all(-1<=s<n for s in r) for r in L['delta'])
    stats.update(variables=len(vars_),dfas=len(langs),dfa_states=sum(len(L['delta']) for L in langs.values()))
    return stats


def evaluate_formula(bundle,model=None):
    """Evaluate one supplied assignment, with no existential search."""
    if model is None:model=bundle.get('grounded_model')
    if model is None:raise ValueError('An explicit model is required')
    def word(T):
        return ''.join(x if kind=='c' else model[x] for kind,x in T)
    def accepts(L,w):
        q=L['start']
        for bit in w:
            q=L['delta'][q][int(bit)]
            if q<0:return False
        return q in L['finals']
    def go(x):
        op=x['op']
        if op=='true':return True
        if op=='false':return False
        if op=='and':return all(go(y) for y in x['args'])
        if op=='or':return any(go(y) for y in x['args'])
        if op=='eq':return word(x['left'])==word(x['right'])
        if op=='reg':return accepts(bundle['languages'][x['language']],word(x['term']))
        raise ValueError('Unknown formula operation')
    for v in bundle['variables']:
        if v not in model or any(a not in '01' for a in model[v]):
            raise ValueError('Missing or nonbinary model variable')
    return go(bundle['formula'])


def example():
    return Instance(((0,1),(0,2),(3,-1),(-1,-1)),0,frozenset({3}),frozenset(),frozenset({(0,2)}))

if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compile-example',metavar='PATH',required=True)
    args=parser.parse_args()
    bundle=compile_scheme(example(),(Phase(0,(0,0)),))
    stats=validate_formula(bundle)
    with open(args.compile_example,'w') as h:json.dump(bundle,h,indent=2);h.write('\n')
    print(json.dumps({'output':args.compile_example,'formula':stats,'solver_executed':False},indent=2))
