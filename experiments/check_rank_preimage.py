"""Compiler audit: full tiny query unions and nested symbolic certificates.

Full general performance, independent mathematical review, and Lean are NOT
claimed. No bounded word search is used as an unrestricted negative oracle.
"""
from collections import Counter
from itertools import product
from pathlib import Path
import argparse,json,random
from border_lab import Instance,words,witness,border_witness
from rank_query_prefix import Reference,ranks_and_milestones
from rank_query_graphs import literal_graph,graph_from_reference,first_return
from rank_preimage import (Budget,Query,Atom,Model,fld,table,model,path,preimages,
    compile_diagram,extract_diagram,reconstruct_reference,verify_assignment,
    finish_queries,interval_observer,decide)
from modular_sync_family import make_family
ROOT=Path(__file__).resolve().parents[1]


def exact(labels):
    return table(len(labels)+1,[(j,a,j+1) for j,a in enumerate(labels)],final=(len(labels),))


def fixed_model(G,Q,assignment):
    if any(not t.holds(G.colours[assignment[v]]) for v,t in Q.tests):return None
    if any(assignment[x]!=assignment[y] for x,y in Q.equal):return None
    if any(assignment[x]==assignment[y] for x,y in Q.unequal):return None
    ps=[]
    for a in Q.atoms:
        p=path(G,a.observer,assignment[a.source],assignment[a.target],Budget(100000))
        if p is None:return None
        ps.append(p)
    return Model(assignment,tuple(ps))


def replay(I,B,V,Q,M,C,others=()):
    D=extract_diagram(I,B,V,Q,M);P=compile_diagram(I,Q,D)
    assert P.weight.bit_length()<=64*(len(I.delta)+Q.weight)**2
    C['compiled_diagrams']+=1;C['compiled_path_atoms']+=len(P.atoms)
    C['largest_observer']=max(C['largest_observer'],max((a.observer.size for a in P.atoms),default=0))
    answer=None
    for i,B2 in enumerate((B,*others)):
        budget=Budget(3000000);sol=model(literal_graph(I,B2),P,budget)
        C['compiled_base_evaluations']+=1
        if sol is None:
            assert i>0;continue
        W,assignment=reconstruct_reference(I,B2,D,P,sol)
        assert graph_from_reference(I,W)==literal_graph(I,W)
        assert verify_assignment(literal_graph(I,W),Q,assignment,budget)
        C['reconstructed_models']+=1;C['reconstructed_atoms']+=len(Q.atoms)
        C['changed_references']+=W.word!=V.word
        C['changed_base_lengths']+=len(B2.word)!=len(B.word)
        C['changed_reference_lengths']+=len(W.word)!=len(V.word)
        if i==0:answer=(P,sol)
    return answer


def check():
    rng=random.Random(2026091737);C=Counter();full=[]
    toy=Instance(((0,0),),frozenset())
    B=Reference('0',(0,0));G=literal_graph(toy,B)
    # These are COMPLETE enumerations over an INFINITE first-return language.
    # F* reaches root; S cannot leave end; K0 cannot reach root of a 0-start
    # pattern; C=00 provides a K1 path to root. These are all-length oracles.
    for label,expected in [('F',True),('S',False),('K0',False),('K1',True)]:
        Q=Query(('x','y'),(('x',fld('end',True)),('y',fld('root',True))),
                atoms=(Atom(table(1,[(0,label,0)]),'x','y'),))
        budget=Budget(2000000);branches=sat=0
        for P in preimages(toy,Q,budget):
            branches+=1;sat+=model(G,P,budget) is not None
        assert bool(sat)==expected
        full.append(dict(label=label,branches=branches,satisfying=sat,work=budget.used,result=expected))
        C['complete_preimage_unions']+=1;C['fully_enumerated_branches']+=branches
    # Two observations of one interval must use the SAME generated letters.
    A=exact(('K0',));D=exact(('K1','K0'))
    assert path(G,interval_observer(toy,(A,),(0,'0',(0,)),(0,'',(1,))),0,G.end) is not None
    assert path(G,interval_observer(toy,(D,),(0,'1',(0,)),(0,'',(2,))),0,G.end) is not None
    for bit in '01':
        joint=interval_observer(toy,(A,D),(0,bit,(0,0)),(0,'',(1,2)))
        assert path(G,joint,0,G.end) is None;C['incompatible_shared_products']=1+C['incompatible_shared_products']
    # Actual compiled queries are grafted onto DIFFERENT base graphs, not only
    # onto different extensions of the same base.
    bases=[Reference(b,(0,)*(len(b)+1)) for b in words('01',3) if b];cases=[]
    for b in bases:
        for length in range(len(b.word)+1,8):
            for tail in product('01',repeat=length-len(b.word)):
                v=b.word+''.join(tail)
                if first_return(b.word,v):cases.append((b,Reference(v,(0,)*(len(v)+1))))
    for trial in range(180):
        B,V=rng.choice(cases);G=literal_graph(toy,V)
        ns=('x','y','z');assignment={v:rng.randrange(len(G.colours)) for v in ns};atoms=[]
        for ai in range(3):
            n=rng.randrange(1,4)
            edges=[(p,a,q) for p in range(n) for q in range(n)
                   for a in ('F','S','K0','K1') if rng.random()<.4]
            o=table(n,edges,final=(rng.randrange(n),));x,y=rng.choice(ns),rng.choice(ns)
            if path(G,o,assignment[x],assignment[y]) is not None:atoms.append(Atom(o,x,y))
        if not atoms:continue
        tests=[]
        for v in ns:
            if rng.random()<.5:
                f=rng.choice(('next_bit','root','end','forbidden'))
                tests.append((v,fld(f,getattr(G.colours[assignment[v]],f))))
        neq=tuple((v,w) for v,w in zip(ns,ns[1:]) if assignment[v]!=assignment[w])
        Q=Query(ns,tuple(tests),unequal=neq,atoms=tuple(atoms));M=fixed_model(G,Q,assignment);assert M
        replay(toy,B,V,Q,M,C,rng.sample(bases,4));C['joint_queries']+=1
    # True terminal references exercise original-state and flag-mask dependence.
    used=0
    for trial in range(180):
        k=rng.randrange(3,8)
        d=tuple(tuple(rng.randrange(-1,k) for _ in '01') for _ in range(k-1))+((-1,-1),)
        flags=frozenset((p,q) for p in range(k) for q in range(k) if rng.random()<.075)
        I=Instance(d,frozenset({k-1}),flags,start=rng.randrange(k))
        for w in words('01',7):
            good=witness(I,w);assert good==border_witness(I,w);C['word_comparisons']+=1
            if not good or not w:continue
            rho=w[::-1];labels=I.run(w)[::-1];_,ms=ranks_and_milestones(rho)
            if len(ms)<2:continue
            j=rng.randrange(len(ms)-1);m,n=ms[j:j+2]
            B=Reference(rho[:m],labels[:m+1]);V=Reference(rho[:n],labels[:n+1])
            o=table(1,[(0,a,0) for a in ('F','S','K0','K1')])
            Q=Query(('x','y'),(('x',fld('end',True)),('y',fld('root',True))),atoms=(Atom(o,'x','y'),))
            M=model(literal_graph(I,V),Q,Budget(100000));assert M
            replay(I,B,V,Q,M,C);used+=1;C['terminal_coloured_compilations']+=1
            if used>=65:break
        if used>=65:break
    nested=[]
    for rank in range(2,8):
        I=make_family((1,)*rank).instance;w='10'*rank
        assert witness(I,w) and border_witness(I,w)
        rho=w[::-1];labels=I.run(w)[::-1]
        refs=[Reference(rho[:m],labels[:m+1]) for m in range(1,2*rank,2)]
        Q=next(q for q in finish_queries(I) if model(literal_graph(I,refs[-1]),q,Budget(100000)))
        weights=[Q.weight]
        for i in range(rank-2,-1,-1):
            B,V=refs[i],refs[i+1];M=model(literal_graph(I,V),Q,Budget(3000000));assert M
            Q,_=replay(I,B,V,Q,M,C);weights.append(Q.weight);C['nested_preimages']+=1
        assert model(literal_graph(I,refs[0]),Q,Budget(3000000)) is not None
        nested.append(dict(rank=rank,states=len(I.delta),witness=w,weights=weights,
                           final_vertices=2,final_atoms=len(Q.atoms)))
    assert decide(Instance(((-1,-1),),frozenset({0})))['word']==''
    assert decide(Instance(((-1,-1),),frozenset({0}),frozenset({(0,0)})))['status']=='NO'
    for n in range(1,8):
        I=Instance(tuple((j+1,-1) for j in range(n))+((-1,-1),),frozenset({n}))
        for m in range(1,n+1):
            B=Reference('0'*m,tuple(range(n,n-m-1,-1)))
            exists=any(model(literal_graph(I,B),Q,Budget(100000)) is not None for Q in finish_queries(I))
            assert exists==(m==n);C['final_return_boundary_checks']+=1
    assert decide(make_family((1,1,1)).instance,max_work=1)['status']=='UNKNOWN';C['caps']=1
    # Complete <=2-state terminal oracle: every positive has an empty or
    # one-letter witness (any safe nonempty path needs the same two labels).
    verdicts=Counter()
    for row in product(range(-1,2),repeat=2):
        for g in range(16):
            flags=frozenset((i//2,i%2) for i in range(4) if g>>i&1)
            for bad in range(4):
                for start in range(2):
                    I=Instance((row,(-1,-1)),frozenset({1}),flags,
                               frozenset(q for q in range(2) if bad>>q&1),start)
                    expected=any(witness(I,w) for w in ('','0','1'))
                    ans=decide(I,max_work=100000)
                    assert ans['status']==('YES' if expected else 'NO')
                    verdicts[ans['status']]+=1;C['complete_two_state_decisions']+=1
    chain=Instance(((1,-1),(2,-1),(-1,-1)),frozenset({2}))
    ans=decide(chain,max_work=100000)
    assert ans['status']=='YES' and ans['word']=='00'
    C['unguided_promoted_positive']=1
    return dict(status='PASS',seed=2026091737,counts=dict(sorted(C.items())),
                full_enumeration=full,nested_compilation=nested,two_state_verdicts=dict(verdicts),
                unguided_chain=ans,
                full_syntactic_enumerator_implemented=True,full_general_algorithm_benchmarked=False,
                scope='Compiler, four complete tiny unions, and nested positive certificates; not external theorem review',
                independent_mathematical_review=False,lean_checked=False)


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,default=ROOT/'results/rank-preimage.json');args=p.parse_args()
    if not __debug__:p.error('Assertions must be enabled')
    out=check();text=json.dumps(out,indent=2,sort_keys=True)+'\n'
    args.output.write_text(text);print(text)
