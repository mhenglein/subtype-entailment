"""Scoped regression: exact template composition and universal-family checking.

Finite oracles are distinguished from all-length arguments.  --with-smt runs
an optional incomplete native backend; timeout is UNKNOWN, not validity or NO.
"""
import argparse
from collections import deque
from dataclasses import replace
from itertools import product
from pathlib import Path
import hashlib
import json
import random

from border_lab import Instance, words, witness, border_witness
from recurrent_residuals import instance, copy_instance, copy_candidate
from shared_word_templates import (Relation,Var,expr,evaluate,compose,lit,cat,alt,star,
    ONE,ZERO,BINARY,path_regex,regex_accepts,family_script,check_family)
from regular_family_safety import check_regular_family
from terminal_realization import realize
from denial_bridge import Canonical

ROOT=Path(__file__).resolve().parents[1]


def equation_pairs(I,w):
    """Independent equation formulation, enumerating cut lengths only."""
    c=I.run(w)
    if c is None: return set()
    answer=set()
    n=len(w)
    for a in range(n+1):
        for b in range(n-a+1):
            x,d,z=w[:a],w[a:a+b],w[a+b:]
            t=(d+z)[len(z):]
            if d+z==z+t:
                answer.add((c[a],c[a+b]))
    return answer


def direct_pairs(I,w):
    c=I.run(w)
    return {(c[i],c[j]) for i in range(len(w)+1) for j in range(i,len(w)+1)
            if w[i:].startswith(w[j:])}


def finite_domain(I):
    assert all(q<0 or q>p for p,row in enumerate(I.delta) for q in row)
    out=[]; stack=[(I.start,'')]
    while stack:
        p,w=stack.pop()
        if p in I.final: out.append(w)
        for a,q in enumerate(I.delta[p]):
            if q>=0: stack.append((q,w+str(a)))
    return out


def assignments(R,max_length):
    choices=[]
    for name,reg in R.domains:
        choices.append([w for w in words('01',max_length) if regex_accepts(reg,w)])
    for vals in product(*choices):
        d=dict(zip((n for n,_ in R.domains),vals))
        if R.satisfies(d): yield d


def relation_set(R,max_length):
    return {(tuple(evaluate(e,d) for e in R.inputs),tuple(evaluate(e,d) for e in R.outputs))
            for d in assignments(R,max_length)}


def dictionary_dfa(dictionary):
    ids={'':0};table=[[-1,-1]];final=set()
    for word in sorted(dictionary):
        p=''
        for a in word:
            q=p+a
            if q not in ids:
                ids[q]=len(table);table.append([-1,-1])
            table[ids[p]][int(a)]=ids[q];p=q
        final.add(ids[p])
    return Instance(tuple(map(tuple,table)),frozenset(final))


def run_core():
    rng=random.Random(2026090660)
    count={'equation_words':0,'equation_annotations':0,'regex_checks':0,
           'composition_cases':0,'associativity_cases':0,'capture_checks':0,'two_output_steps':0,
           'complete_finite_oracles':0,'finite_family_words':0,
           'cyclic_tables':0,'cyclic_word_checks':0,'canonical_checks':0,'caps':0,
           'nonterminal_oracles':0,'nonterminal_words':0,'nonterminal_analytic':0}
    # Arbitrary (not necessarily terminal) tables exercise overlaps and boundaries.
    for _ in range(120):
        k=rng.randrange(1,6)
        I=Instance(tuple(tuple(rng.randrange(-1,k) for _ in (0,1)) for _ in range(k)),
                   frozenset(p for p in range(k) if rng.random()<.6),
                   frozenset((p,q) for p in range(k) for q in range(k) if rng.random()<.15),
                   frozenset(p for p in range(k) if rng.random()<.08),rng.randrange(k))
        for w in words('01',7):
            c=I.run(w)
            if c is not None:
                A=equation_pairs(I,w)
                assert A==direct_pairs(I,w)
                count['equation_words']+=1
                assert (I.admissible(w) and not I.flags&A)==witness(I,w)==border_witness(I,w)
                count['equation_annotations']+=1
        # Path regex is tested against direct paths, independently of SMT.
        a=rng.randrange(k); finals=tuple(p for p in range(k) if rng.random()<.5)
        reg=path_regex(I.delta,a,finals)
        J=replace(I,start=a,final=frozenset(finals),flags=frozenset(),bad=frozenset())
        for w in words('01',6):
            assert regex_accepts(reg,w)==J.admissible(w)
            count['regex_checks']+=1
    # Composition and accidental name-capture checks, complete finite domains.
    X,Y=Var('X'),Var('Y')
    vocab=('','0','1','01')
    for _ in range(60):
        ds=[tuple(rng.sample(vocab,rng.randrange(1,4))) for _ in range(4)]
        regs=[alt(*(lit(w) for w in d)) for d in ds]
        L=Relation((('X',regs[0]),('Y',regs[1])),(expr(X),),(expr(Y,X),))
        R=Relation((('X',regs[2]),('Y',regs[3])),(expr(X,Y),),(expr(Y),))
        l,r=relation_set(L,2),relation_set(R,2)
        expected={(x,z) for x,y in l for y2,z in r if y==y2}
        assert relation_set(compose(L,R),2)==expected
        count['composition_cases']+=1
    finite=alt(*(lit(w) for w in ('','0','1')))
    for _ in range(12):
        # One variable per relation; tests semantic associativity, not names.
        cs=[rng.choice(('','0','1')) for _ in range(3)]
        Rs=[Relation((('X',finite),),(expr(X),),(expr(X,c),)) for c in cs]
        assert relation_set(compose(compose(Rs[0],Rs[1]),Rs[2]),1)==relation_set(compose(Rs[0],compose(Rs[1],Rs[2])),1)
        count['associativity_cases']+=1
    A=Relation((('X',lit('0')),),(expr(X),),(expr('1'),))
    B=Relation((('X',lit('1')),),(expr(X),),(expr('0'),))
    assert relation_set(compose(A,B),1)=={(('0',),('0',))}
    count['capture_checks']+=1
    # Generic iteration has a PCP-shaped two-output accumulation mechanism.
    T0=Relation((('X',BINARY),('Y',BINARY)),(expr(X),expr(Y)),(expr(X,'0'),expr(Y,'01')))
    T1=Relation((('X',BINARY),('Y',BINARY)),(expr(X),expr(Y)),(expr(X,'10'),expr(Y,'0')))
    joined=compose(T0,T1)
    subst={'l_X':'','l_Y':'','r_X':'0','r_Y':'01'}
    assert joined.satisfies(subst)
    assert tuple(evaluate(e,subst) for e in joined.inputs)==('','')
    assert tuple(evaluate(e,subst) for e in joined.outputs)==('010','010')
    count['two_output_steps']+=1
    # Independent, complete finite-domain oracle for the monoid procedure.
    outcomes={'REGULAR_FAMILY_VALID':0,'COUNTEREXAMPLE':0,'UNKNOWN':0}
    for _ in range(320):
        k=rng.randrange(2,6)
        I=Instance(tuple(tuple(rng.randrange(-1,k) for _ in (0,1)) for _ in range(k-1))+((-1,-1),),
                   frozenset({k-1}),
                   frozenset((p,q) for p in range(k) for q in range(k) if rng.random()<.08),
                   frozenset(p for p in range(k) if rng.random()<.03))
        dictionary=tuple(rng.sample(tuple(words('01',4)),rng.randrange(0,8)))
        D=dictionary_dfa(dictionary)
        expected=all(witness(I,w) for w in dictionary)
        count['finite_family_words']+=len(dictionary)
        out=check_regular_family(I,D,max_monoid=None,max_trials=None)
        assert out['status']!='UNKNOWN' and (out['status']=='REGULAR_FAMILY_VALID')==expected,(I,D,out,dictionary)
        count['complete_finite_oracles']+=1;outcomes[out['status']]+=1
    # More finite domains chosen inside accepting languages, so monoid rejection
    # rather than mere admissibility is exercised.
    for _ in range(100):
        k=4
        table=tuple(tuple(rng.randrange(-1,k) for _ in (0,1)) for _ in range(k-1))+((-1,-1),)
        I=Instance(table,frozenset({k-1}))
        pool=[w for w in words('01',5) if I.admissible(w)]
        if not pool: continue
        dictionary=tuple(rng.sample(pool,min(len(pool),rng.randrange(1,7))))
        I=replace(I,flags=frozenset((p,q) for p in range(k-1) for q in range(k-1) if p!=q and rng.random()<.3))
        D=dictionary_dfa(dictionary)
        out=check_regular_family(I,D,max_monoid=None,max_trials=None)
        expected=all(witness(I,w) for w in dictionary)
        assert out['status']!='UNKNOWN' and (out['status']=='REGULAR_FAMILY_VALID')==expected
        count['finite_family_words']+=len(dictionary)
        count['complete_finite_oracles']+=1;outcomes[out['status']]+=1
    # Every three-state terminal transition table, tested against all short words.
    # This is bounded validation, NOT an independent all-length oracle.
    cyc={'REGULAR_FAMILY_VALID':0,'COUNTEREXAMPLE':0,'UNKNOWN':0}
    for entries in product(range(-1,3),repeat=4):
        table=(entries[:2],entries[2:],(-1,-1))
        I=Instance(table,frozenset({2}),frozenset({(0,1)}))
        D=replace(I,flags=frozenset())
        out=check_regular_family(I,D,max_monoid=None,max_trials=None)
        cyc[out['status']]+=1;count['cyclic_tables']+=1
        for w in words('01',7):
            if D.admissible(w):
                if out['status']=='REGULAR_FAMILY_VALID': assert witness(I,w)
                count['cyclic_word_checks']+=1
        if out['status']=='COUNTEREXAMPLE':
            assert D.admissible(out['word']) and not witness(I,out['word'])
    # Explicit whole-language analytic benchmarks, not guessed cutoffs.
    I=instance()
    D=Instance(((-1,1),(2,-1),(2,3),(4,-1),(-1,-1)),frozenset({4}))
    safe=check_regular_family(I,D,max_monoid=None,max_trials=None)
    assert safe['status']=='REGULAR_FAMILY_VALID' and safe['inhabited']
    mixed=check_regular_family(I,replace(I,flags=frozenset()),max_monoid=None,max_trials=None)
    assert mixed['status']=='COUNTEREXAMPLE'
    noflags=check_regular_family(replace(I,flags=frozenset()),replace(I,flags=frozenset()),max_monoid=None,max_trials=None)
    assert noflags['status']=='REGULAR_FAMILY_VALID'
    cap=check_regular_family(I,D,max_monoid=1)
    assert cap['status']=='UNKNOWN';count['caps']+=1
    notterminal=Instance(((0,0),),frozenset({0}))
    universal_nonterminal=check_regular_family(notterminal,notterminal,max_monoid=None,max_trials=None)
    assert universal_nonterminal['status']=='REGULAR_FAMILY_VALID' and universal_nonterminal['inhabited']
    count['nonterminal_analytic']+=1
    even=Instance(((1,-1),(0,-1)),frozenset({0}),frozenset({(0,1)}))
    positive_even=Instance(((1,-1),(2,-1),(1,-1)),frozenset({2}))
    nonterminal_bad=check_regular_family(even,positive_even,max_monoid=None,max_trials=None)
    assert nonterminal_bad['status']=='COUNTEREXAMPLE' and nonterminal_bad['word']=='00'
    assert nonterminal_bad['factorization']['exponent']==2
    count['nonterminal_analytic']+=1
    # Separate seed preserves all earlier random coverage. Finite domains make
    # these complete oracles even though the I final states have outgoing edges.
    rng_nt=random.Random(2026090662)
    nt={'REGULAR_FAMILY_VALID':0,'COUNTEREXAMPLE':0,'UNKNOWN':0}
    for _ in range(320):
        k=rng_nt.randrange(1,6)
        M=Instance(tuple(tuple(rng_nt.randrange(-1,k) for _ in (0,1)) for _ in range(k)),
                   frozenset(q for q in range(k) if rng_nt.random()<.6),
                   frozenset((p,q) for p in range(k) for q in range(k) if rng_nt.random()<.1),
                   frozenset(q for q in range(k) if rng_nt.random()<.04),rng_nt.randrange(k))
        dictionary=tuple(rng_nt.sample(tuple(words('01',4)),rng_nt.randrange(0,8)))
        out=check_regular_family(M,dictionary_dfa(dictionary),max_monoid=None,max_trials=None)
        assert out['status']!='UNKNOWN' and (out['status']=='REGULAR_FAMILY_VALID')==all(witness(M,w) for w in dictionary)
        nt[out['status']]+=1;count['nonterminal_oracles']+=1;count['nonterminal_words']+=len(dictionary)
    # Exact canonical model validation for representative complete words.
    for M,ws in [(I,('1010','10110','11010','10010')), (copy_instance(),(copy_candidate('0','0'),copy_candidate('0','1')))]:
        R=realize(M)
        for w in ws:
            good=not Canonical(R.variables,R.constraints,R.alpha,R.beta,w).errors()
            assert good==witness(M,w)
            count['canonical_checks']+=1
    return {'status':'PASS','seed':2026090660,'counts':count,
            'finite_oracle_verdicts':outcomes,'cyclic_bounded_checks':cyc,'arbitrary_final_oracles':nt,
            'fixtures':{'infinite_regular_safe_family':safe,'mixed_family':mixed,'all_noflag_candidates':noflags,'cap':cap,
                        'nonterminal_universal':universal_nonterminal,'nonterminal_period_two':nonterminal_bad},
            'proof_status':'Written arguments and external word-equation theorem; no Lean or independent review',
            'scope':'Universal validation of supplied families, not unrestricted existential decision'}


def run_smt():
    X,Y,N=map(Var,('X','Y','N'))
    I=instance(); C=copy_instance()
    protected=Instance(((1,-1),(2,-1),(4,3),(2,2),(-1,5),(-1,-1)),frozenset({5}),frozenset({(0,2)}))
    fixtures=[
      ('shared_nonflat_protected',protected,Relation((('X',star(alt(lit('10'),lit('11')))),),(),()),expr('00',X,X,'01')),
      ('valid_singleton',I,Relation((),(),()),expr('1010')),
      ('bad_singleton',I,Relation((),(),()),expr('10110')),
      ('empty_domain',I,Relation((('X',None),),(),()),expr(X)),
      ('infinite_regular_family',I,Relation((('Y',cat(ZERO,star(ZERO))),),(),()),expr('1',Y,'10')),
      ('independent_parameters',I,Relation((('X',cat(ONE,star(ONE))),('Y',cat(ONE,star(ONE)))),(),()),expr(X,'0',Y,'0')),
      ('shared_unbounded_unary',I,Relation((('X',cat(ONE,star(ONE))),('Y',cat(ZERO,star(ZERO)))),(),()),expr(X,Y,X,'0')),
      ('shared_unbounded_copy',C,Relation((('X',star(alt(lit('10'),lit('11')))),('N',star(lit('01')))),(),()),expr(X,'00',N,X,'00')),
      ('independent_copy',C,Relation((('X',star(alt(lit('10'),lit('11')))),('Y',star(alt(lit('10'),lit('11'))))),(),()),expr(X,'00',Y,'00')),
    ]
    rows=[]
    for name,M,R,w in fixtures:
        query=family_script(M,R,w,timeout_ms=1500)
        assert not any(bad in query for bad in ('str.len','str.substr','forall','exists','str.prefixof','str.contains'))
        querydir=ROOT/'results'/'shared-composition-queries'
        querydir.mkdir(parents=True,exist_ok=True)
        (querydir/f'{name}.smt2').write_text(query)
        out=check_family(M,R,w,timeout_ms=1500,wall_seconds=4)
        rows.append({'name':name,'result':out})
        if name=='shared_nonflat_protected': assert out['status'] in ('VALID_FAMILY_SMT','UNKNOWN')
        if name=='valid_singleton': assert out['status']=='VALID_FAMILY_SMT'
        if name=='bad_singleton': assert out['status']=='COUNTEREXAMPLE'
        if name=='empty_domain': assert out['status']=='VACUOUS_SMT'
        if name in ('shared_unbounded_unary','shared_unbounded_copy','infinite_regular_family'):
            assert out['status'] in ('VALID_FAMILY_SMT','UNKNOWN')
        if name.startswith('independent'):
            assert out['status'] in ('COUNTEREXAMPLE','UNKNOWN')
    # Complete finite-family oracles, rather than sampled unbounded parameters.
    rng=random.Random(2026090661); checked=0; unresolved=0
    vocab=('1','11','111')
    for trial in range(20):
        left=tuple(rng.sample(vocab,rng.randrange(1,4)))
        right=tuple(rng.sample(vocab,rng.randrange(1,4)))
        linked=bool(trial%2)
        R=Relation((('X',alt(*(lit(w) for w in left))),('Y',alt(*(lit(w) for w in right)))),(),(),
                   ((expr(X),expr(Y)),) if linked else ())
        ws=[evaluate(expr(X,'0',Y,'0'),d) for d in assignments(R,3)]
        out=check_family(I,R,expr(X,'0',Y,'0'),timeout_ms=700,wall_seconds=3)
        if out['status']=='UNKNOWN': unresolved+=1;continue
        expected='VACUOUS_SMT' if not ws else 'VALID_FAMILY_SMT' if all(witness(I,w) for w in ws) else 'COUNTEREXAMPLE'
        assert out['status']==expected,(trial,ws,out)
        checked+=1
    return {'status':'PASS','backend_limit_ms':1500,'fixtures':rows,
            'finite_family_oracles':checked,'finite_family_unknown':unresolved,
            'warning':'Native Z3 is incomplete; UNKNOWN is retained. UNSAT uses backend trust, not proof checking.'}


def main():
    p=argparse.ArgumentParser();p.add_argument('--with-smt',action='store_true');args=p.parse_args()
    result=run_core()
    if args.with_smt: result['optional_smt']=run_smt()
    result['dependency_blobs']={name:hashlib.sha1(('blob %d\0'%len(raw)).encode()+raw).hexdigest()
        for name in ('border_lab.py','recurrent_residuals.py','terminal_realization.py','denial_bridge.py')
        for raw in [(ROOT/'experiments'/name).read_bytes()]}
    name='shared-composition-smt.json' if args.with_smt else 'shared-composition.json'
    (ROOT/'results'/name).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
