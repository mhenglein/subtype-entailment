"""Positive existential formulas for supplied source-cycle power schemes.

This is an exact compiler, not a complete constrained-word-equation backend
and not an automatic finite cover for arbitrary terminal instances. A phase
repeats one unknown source-simple first-return cycle word. Different phases
may use different words. All occurrences within one phase share that word.
"""
from dataclasses import dataclass
from functools import lru_cache
import json
from shared_word_templates import path_regex, regex_smt, BINARY, cat, alt, ZERO, ONE
from source_power import validate

NONEMPTY = cat(alt(ZERO, ONE), BINARY)
EMPTY = '""'


def And(*xs):
    ys = [x for x in xs if x != 'true']
    return 'false' if 'false' in ys else 'true' if not ys else ys[0] if len(ys)==1 else '(and '+' '.join(ys)+')'


def Or(*xs):
    ys = [x for x in xs if x != 'false']
    return 'true' if 'true' in ys else 'false' if not ys else ys[0] if len(ys)==1 else '(or '+' '.join(ys)+')'


def Eq(a,b): return '(= '+a+' '+b+')'


def Con(*xs):
    ys = [x for x in xs if x != EMPTY]
    return EMPTY if not ys else ys[0] if len(ys)==1 else '(str.++ '+' '.join(ys)+')'


def literal(w):
    if not isinstance(w,str) or any(a not in '01' for a in w):
        raise ValueError('Binary literal required')
    return json.dumps(w)


@dataclass(frozen=True)
class Phase:
    pivot: int
    # None means one ordinary visit; otherwise distinct source labels in a
    # cyclic order starting at pivot. Each gap has no interior source visit.
    cycle: tuple = None


class Compiler:
    def __init__(self,I):
        validate(I)
        self.I=I;self.k=len(I.delta)
        self.safe=tuple(tuple(q if p not in I.bad and q not in I.bad else -1 for q in row)
                        for p,row in enumerate(I.delta))
        self.sources={p for p,_ in I.flags}
        self.variables=[]
        self.counter=0

    def var(self,hint='v'):
        self.counter+=1
        name=hint+'_'+str(self.counter)
        self.variables.append(name)
        return name

    def mem(self,w,rx):
        return 'false' if rx is None else '(str.in_re '+w+' '+regex_smt(rx)+')'

    def nonempty(self,w):return self.mem(w,NONEMPTY)

    @lru_cache(maxsize=None)
    def path(self,p,finals):
        return None if p in self.I.bad else path_regex(self.safe,p,tuple(sorted(set(finals)-self.I.bad)))

    @lru_cache(maxsize=None)
    def no_capture(self,t):
        n=self.k; hit=n; miss=n+1
        rows=[]
        for q in range(n):
            if q in self.I.bad: rows.append((miss,miss));continue
            if q in self.I.final: rows.append((hit,hit));continue
            rows.append(tuple(miss if r<0 or r in self.I.bad else hit if r in self.I.final else r
                              for r in self.safe[q]))
        rows.extend(((hit,hit),(miss,miss)))
        start=miss if t in self.I.bad else hit if t in self.I.final else t
        return path_regex(tuple(rows),start,tuple(q for q in range(n+2) if q!=hit))

    @lru_cache(maxsize=None)
    def first_return(self,p):
        if p in self.I.bad:return None
        rows=list(self.safe)
        rows[p]=(-1,-1)
        rows.append(self.safe[p])
        return path_regex(tuple(rows),self.k,(p,))

    @lru_cache(maxsize=None)
    def boundary_path(self,p,s,targets):
        n=self.k;T=set(targets)
        if p in self.I.bad or s in self.I.bad or s in T:return None
        def ok(a,b):return a not in self.I.bad and b not in self.I.bad and not(a==p and b in T)
        rows=[]
        for a in range(n):
            for b in range(n):
                row=[]
                for bit in range(2):
                    c,d=self.safe[a][bit],self.safe[b][bit]
                    row.append(c*n+d if ok(a,b) and c>=0 and d>=0 and ok(c,d) else -1)
                rows.append(tuple(row))
        return path_regex(tuple(rows),p*n+s,tuple(a*n+b for a in range(n) for b in range(n) if ok(a,b)))

    def not_suffix(self,V,W):
        # Either W is a proper suffix of V or right-aligned letters differ.
        r=self.var('long')
        cases=[And(Eq(V,Con(r,W)),self.nonempty(r))]
        for a,b in (('0','1'),('1','0')):
            r,s,z=self.var('left'),self.var('right'),self.var('common')
            cases.append(And(Eq(V,Con(r,literal(a),z)),Eq(W,Con(s,literal(b),z))))
        return Or(*cases)

    def phi(self,p,t,W):
        # C067's unique prefix capture, at ONE specified source position.
        V,X,Q=self.var('capture'),self.var('rest'),self.var('cut')
        return Or(self.mem(W,self.no_capture(t)),
                  And(Eq(W,Con(V,X)),self.mem(V,self.path(t,tuple(self.I.final))),
                      Or(self.not_suffix(V,W),And(Eq(W,Con(Q,V)),self.mem(Q,self.path(p,tuple(q for q in range(self.k) if q!=t)))))))

    def local_safe(self,p,W):
        return And(*(self.phi(p,t,W) for q,t in sorted(self.I.flags) if q==p))

    def powers(self,p,B,U):
        return And(Eq(Con(U,B),Con(B,U)),self.mem(U,self.path(p,(p,))))

    def boundary_guard(self,p,T,Z,K):
        targets=tuple(sorted(T))
        return Or(*(And(self.mem(Z,self.path(p,(s,))),self.mem(K,self.boundary_path(p,s,targets)))
                    for s in range(self.k)))

    def good_conjugacies(self,p,T,B,U,Q):
        A,K,J,D=(self.var(x) for x in ('remainder','suffixpower','difference','exceptioncut'))
        # Q=A B^ell with A not ending in B; K=B^ell. U=B^m.
        maximal=And(Eq(Q,Con(A,K)),self.powers(p,B,K),self.not_suffix(B,A))
        first=And(Eq(K,Con(J,U)),self.boundary_guard(p,T,Con(A,J),U))
        exceptional=Or(self.not_suffix(B,Con(B,A)),
                       And(Eq(Con(B,A),Con(D,B)),self.mem(D,self.path(p,tuple(q for q in range(self.k) if q not in T)))))
        second=And(Eq(U,Con(K,J)),self.nonempty(J),self.boundary_guard(p,T,A,K),exceptional)
        return And(maximal,Or(first,second))

    def repeated_safe(self,p,B,U,Y):
        """All displayed source boundaries of UY, U=B^m; no other sources."""
        T={t for q,t in self.I.flags if q==p}
        clauses=[self.mem(B,self.first_return(p)),self.powers(p,B,U),
                 self.mem(Y,self.path(p,tuple(self.I.final))),self.local_safe(p,Con(U,Y))]
        if not T:return And(*clauses)
        for r in range(self.k):
            P,X,Q=(self.var(h) for h in ('border','tailrest','tailprefix'))
            good=Or(Eq(P,EMPTY),self.not_suffix(P,Y),
                    And(Eq(Y,Con(Q,P)),
                        Or(self.mem(Q,self.path(p,tuple(q for q in range(self.k) if q!=r))),
                           self.good_conjugacies(p,T,B,U,Q))))
            clauses.append(Or(self.mem(Y,self.no_capture(r)),
                              And(Eq(Y,Con(P,X)),self.mem(P,self.path(r,tuple(self.I.final))),good)))
        return And(*clauses)

    @lru_cache(maxsize=None)
    def next_source(self,p,q):
        # Positive safe path p -> q, with NO source at an interior position.
        rows=[]
        for a,row in enumerate(self.safe):
            rows.append((-1,-1) if a in self.sources else
                        tuple(t if t not in self.sources or t==q else -1 for t in row))
        rows.append(tuple(t if t not in self.sources or t==q else -1 for t in self.safe[p]))
        return path_regex(tuple(rows),self.k,(q,)) if p not in self.I.bad and q not in self.I.bad else None

    def entry(self,q):
        if self.I.start in self.I.bad:return None
        if self.I.start in self.sources:
            return ('lit','') if self.I.start==q else None
        rows=tuple((-1,-1) if p in self.sources else tuple(t if t not in self.sources or t==q else -1 for t in row)
                   for p,row in enumerate(self.safe))
        return path_regex(rows,self.I.start,(q,))

    def final_tail(self,p):
        rows=tuple(tuple(t if t not in self.sources else -1 for t in row) for row in self.safe)
        return path_regex(rows,p,tuple(self.I.final-self.I.bad)) if p not in self.I.bad else None

    def scheme(self,phases):
        phases=tuple(phases)
        if not phases:raise ValueError('At least one phase required; source-free words use regular reachability')
        for phase in phases:
            if phase.pivot not in self.sources:raise ValueError('Pivots must be flagged-source states')
            if phase.cycle is not None:
                if not phase.cycle or phase.cycle[0]!=phase.pivot or len(set(phase.cycle))!=len(phase.cycle) or not set(phase.cycle)<=self.sources:
                    raise ValueError('A cycle is a distinct-source list starting at its pivot')
        entry=self.var('entry')
        bundles=[self.var('power') for _ in phases]
        bridges=[self.var('bridge') for _ in phases]
        tails=[Con(*(x for j in range(i,len(phases)) for x in ((bridges[j],) if j==i else (bundles[j],bridges[j])))) for i in range(len(phases))]
        out=self.var('word')
        clauses=[self.mem(entry,self.entry(phases[0].pivot)),Eq(out,Con(entry,bundles[0],tails[0]))]
        bases=[]
        for i,phase in enumerate(phases):
            p=phase.pivot;U=bundles[i];Y=tails[i]
            clauses.append(self.mem(bridges[i],self.next_source(p,phases[i+1].pivot) if i+1<len(phases) else self.final_tail(p)))
            clauses.append(self.local_safe(p,Y)) # source at exit of the repeated phase
            if phase.cycle is None:
                clauses.append(Eq(U,EMPTY));bases.append(None);continue
            cycle=phase.cycle
            segments=[self.var('segment') for _ in cycle]
            B=self.var('base');bases.append((B,segments))
            active=[self.nonempty(U),Eq(B,Con(*segments)),self.powers(p,B,U)]
            for j,q in enumerate(cycle):
                active.append(self.mem(segments[j],self.next_source(q,cycle[(j+1)%len(cycle)])))
                A=Con(*segments[:j]);C=Con(*segments[j:]);R=Con(C,A)
                V=self.var('rotatedpower')
                active.append(Eq(U,Con(A,V,C)))
                active.append(self.repeated_safe(q,R,V,Con(C,Y)))
            clauses.append(Or(Eq(U,EMPTY),And(*active)))
        return And(*clauses),dict(word=out,entry=entry,powers=bundles,bridges=bridges,bases=bases,
                                 phases=[dict(pivot=p.pivot,cycle=p.cycle) for p in phases])

    def script(self,formula,extra=(),timeout_ms=3000):
        if type(timeout_ms) is not int or timeout_ms<1:raise ValueError('Positive timeout required')
        lines=['(set-logic QF_SLIA)','(set-option :produce-models true)',
               '(set-option :timeout %d)'%timeout_ms,'(set-option :smt.string_solver seq)']
        for v in self.variables:
            lines+=['(declare-const '+v+' String)','(assert '+self.mem(v,BINARY)+')']
        lines+=['(assert '+formula+')']+['(assert '+x+')' for x in extra]+['(check-sat)']
        return '\n'.join(lines)+'\n'
