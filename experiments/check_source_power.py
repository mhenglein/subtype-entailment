"""Reproduce source-power algebra, boundary reduction, and optional formulas.

Default output is deterministic and uses only the standard library. Optional
SMT results retain UNKNOWN and solver trust; they are not the decision theorem.
"""
import hashlib
import itertools
import json
import random
import sys
from dataclasses import replace
from pathlib import Path
from border_lab import Instance, words, witness, border_witness
from source_power import (run_from, power_context, conjugacy_cut, conjugacy_summary,
                          captured_borders, boundary_targets, direct_boundary_targets,
                          boundary_safe)

ROOT=Path(__file__).resolve().parents[1]


def reverse_boundary_targets(I,p,B,Y,m):
    w=B*m+Y;c=run_from(I,p,w)[::-1];rho=w[::-1];n=len(w)
    origins={n-i for i in range(0,m*len(B)+1,len(B))}
    return {c[b] for a in origins for b in range(a+1)
            if rho[:b]==rho[a-b:a]}


def exception_instance():
    return Instance(((1,3),(-1,2),(0,-1),(4,-1),(-1,5),(-1,-1)),
                    frozenset({5}),frozenset({(0,2)}))


def core():
    rng=random.Random(2026091072)
    counts=dict(conjugacy_identities=0,three_state_loop_contexts=0,
                boundary_comparisons=0,capture_border_checks=0,
                first_return_commutations=0,random_contexts=0,
                large_exponent_checks=0,rotation_checks=0,
                two_cycle_profiles=0,guard_cases=0,canonical_paths=0)
    for B in words('01',5):
        if not B:continue
        for Q in words('01',7):
            for j in range(11):
                assert conjugacy_cut(B,Q,j)==conjugacy_summary(B,Q,j),(B,Q,j)
                counts['conjugacy_identities']+=1
    short=tuple(words('01',4));uwords=tuple(words('01',6));pool=[]
    def compare(I,p,B,Y):
        direct={l for l in range(1,len(Y)+1) if Y[:l]==Y[-l:]}
        captured=captured_borders(I,p,Y)
        assert direct=={len(P) for P,Q in captured.values()}
        counts['capture_border_checks']+=1
        for m in (0,1,2,3,5,9):
            ans=boundary_targets(I,p,B,Y,m)
            a=direct_boundary_targets(I,p,B,Y,m)
            b=reverse_boundary_targets(I,p,B,Y,m)
            assert set(ans)==a==b,(I,p,B,Y,m,ans,a,b)
            for t,(j,d,kind) in ans.items():
                s=B*j+Y;c=run_from(I,p,s)
                assert j<=m and c[d]==t and s.startswith(s[d:]),(t,j,d,kind)
            counts['boundary_comparisons']+=1
        M=max(len(I.delta),len(Y)//len(B)+1)
        assert set(boundary_targets(I,p,B,Y,10**60))==set(boundary_targets(I,p,B,Y,M))
        counts['large_exponent_checks']+=1
    for tr in itertools.product(range(-1,3),repeat=4):
        I=Instance((tr[:2],tr[2:],(-1,-1)),frozenset({2}))
        for p in range(2):
            loops=[w for w in short if w and (c:=run_from(I,p,w)) is not None and c[-1]==p]
            tails=[w for w in short if (c:=run_from(I,p,w)) is not None and c[-1]==2]
            for B in loops:
                cb=run_from(I,p,B)
                if p not in cb[1:-1]:
                    for U in uwords:
                        cu=run_from(I,p,U)
                        left=cu is not None and cu[-1]==p and U+B==B+U
                        right=len(U)%len(B)==0 and U==B*(len(U)//len(B))
                        assert left==right,(I,p,B,U)
                        counts['first_return_commutations']+=1
            if loops and tails:pool.append((I,p,loops,tails))
            for B,Y in itertools.product(loops,tails):
                compare(I,p,B,Y);counts['three_state_loop_contexts']+=1
    for _ in range(240):
        k=rng.randrange(4,8);p=rng.randrange(k-1)
        rows=tuple(tuple(rng.randrange(-1,k) for _ in range(2)) for q in range(k-1))+((-1,-1),)
        bad=frozenset(q for q in range(k) if rng.random()<.06)
        I=Instance(rows,frozenset({k-1}),bad=bad,start=p)
        candidates=tuple(words('01',5))
        loops=[w for w in candidates if w and (c:=run_from(I,p,w)) and c[-1]==p]
        tails=[w for w in candidates if (c:=run_from(I,p,w)) and c[-1]==k-1]
        if not loops or not tails:continue
        for _ in range(3):
            B,Y=rng.choice(loops),rng.choice(tails)
            compare(I,p,B,Y);counts['random_contexts']+=1
            for a in range(len(B)):
                A,C=B[:a],B[a:];R=C+A;q=run_from(I,p,A)[-1]
                for m in (1,2,5):
                    assert B*m==A+R*(m-1)+C
                    # No first-return assumption is needed for concrete rotation.
                    assert set(boundary_targets(I,q,R,C+Y,m-1))==direct_boundary_targets(I,q,R,C+Y,m-1)
                    counts['rotation_checks']+=1
    # All source positions are partitioned between two simple-source cycles
    # and their exits. This checks full profiles, not just selected flags.
    two=Instance(((1,2),(0,-1),(4,3),(-1,2),(-1,-1)),frozenset({4}))
    for m,n in itertools.product(range(9),repeat=2):
        w='00'*m+'1'+'11'*n+'0';c=two.run(w)
        target={}
        Y0='1'+'11'*n+'0'
        # Finite phase-exit sources 0 and 2.
        for p,Y in ((0,Y0),(2,'0')):
            d=run_from(two,p,Y)
            target.setdefault(p,set()).update(d[j] for j in range(len(Y)+1) if Y.startswith(Y[j:]))
        for p,B,Y,copies in ((0,'00','00'+Y0,m),(1,'00','0'+Y0,m),
                              (2,'11','110',n),(3,'11','10',n)):
            if copies:target.setdefault(p,set()).update(boundary_targets(two,p,B,Y,copies-1))
        target[4]={4}
        profile={(p,t) for p,ts in target.items() for t in ts}
        direct={(c[i],c[j]) for i in range(len(w)+1) for j in range(i,len(w)+1) if w[i:].startswith(w[j:])}
        assert profile==direct,(m,n,profile,direct)
        counts['two_cycle_profiles']+=1
    I=exception_instance();B='010';Y='101';w=B*2+Y
    assert not witness(I,w) and not border_witness(I,w)
    assert all((0,I.run(w)[j]) not in I.flags or not w.startswith(w[j:]) for j in range(len(w)+1))
    cert=boundary_targets(I,0,B,Y,2)[2]
    assert cert==(1,2,'exceptional')
    # Return-free is not literal primitivity: 00 can first-return at 0.
    assert run_from(two,0,'00')==(0,1,0)
    assert '0'+'00'=='00'+'0' and run_from(two,0,'0')[-1]!=0
    # Without the first-return guard the centralizer is too large.
    bad_base=Instance(((0,1),(-1,-1)),frozenset({1}))
    assert run_from(bad_base,0,'0')[-1]==0 and '0'+'00'=='00'+'0'
    assert '0'!='00'*(len('0')//2)
    counts['guard_cases']+=2
    for badcall in (lambda:boundary_targets(two,0,'','10',1),
                    lambda:boundary_targets(two,0,'00','10',-1),
                    lambda:boundary_targets(two,0,'0','10',1),
                    lambda:boundary_targets(Instance(((0,0),),frozenset({0})),0,'0','',1)):
        try:badcall();raise AssertionError('Missing input guard')
        except ValueError:counts['guard_cases']+=1
    from terminal_realization import realize
    from denial_bridge import Canonical
    for inst in (I,replace(two,flags=frozenset({(0,2),(2,1)}))):
        R=realize(inst)
        ws=('101','010101','010010101') if inst is I else ('10','0010','1110')
        for word in ws:
            assert (not Canonical(R.variables,R.constraints,R.alpha,R.beta,word).errors())==witness(inst,word)
            counts['canonical_paths']+=1
    def blob(p):
        b=(ROOT/'experiments'/p).read_bytes()
        return hashlib.sha1(('blob %d\0'%len(b)).encode()+b).hexdigest()
    return dict(status='PASS',seed=2026091072,counts=counts,
                exceptional_fixture=dict(delta=I.delta,flags=sorted(I.flags),base=B,tail=Y,
                                         word=w,earliest_source_valid=True,witness=False,
                                         certificate=cert),
                huge_exponent=10**60,
                dependency_blobs={p:blob(p) for p in ('border_lab.py','terminal_realization.py','denial_bridge.py')},
                proof_status='Written all-length arguments; not independently reviewed or Lean-checked',
                scope='Boundary-origin reduction and supplied finite power schemes; not unrestricted coverage')


def optional_smt():
    from source_power_formula import Compiler,Phase,Eq,literal
    from shared_word_templates import run_script
    rng=random.Random(719);ws=tuple(words('01',3));pool=[];out=[]
    for tr in itertools.product(range(-1,3),repeat=4):
        I=Instance((tr[:2],tr[2:],(-1,-1)),frozenset({2}))
        for p in range(2):
            loops=[w for w in ws if w and (c:=run_from(I,p,w)) and c[-1]==p and p not in c[1:-1]]
            tails=[w for w in ws if (c:=run_from(I,p,w)) and c[-1]==2]
            if loops and tails:pool.append((I,p,loops,tails))
    for i in range(16):
        I,p,loops,tails=rng.choice(pool);B=rng.choice(loops);Y=rng.choice(tails);m=rng.randrange(4)
        T=frozenset(q for q in range(3) if rng.random()<.4)
        I=replace(I,flags=frozenset((p,t) for t in T))
        expected=boundary_safe(I,p,B,Y,m)
        C=Compiler(I);b,u,y=(C.var(s) for s in ('B','U','Y'))
        f=C.repeated_safe(p,b,u,y)
        script=C.script(f,[Eq(b,literal(B)),Eq(u,literal(B*m)),Eq(y,literal(Y))],timeout_ms=500)
        result=run_script(script,[b,u,y],wall_seconds=2)
        assert result['status']=='UNKNOWN' or (result['status']=='SAT')==expected,(I,p,B,Y,m,result)
        out.append(dict(name='ground_'+str(i),expected=expected,result=result))
    I=exception_instance();C=Compiler(I);b,u,q=(C.var(n) for n in ('B','U','Q'))
    f=C.good_conjugacies(0,{2},b,u,q)
    result=run_script(C.script(f,[Eq(b,literal('010')),Eq(u,literal('010010')),Eq(q,literal('10'))],timeout_ms=3000),[b,u,q],wall_seconds=5)
    assert result['status'] in ('UNSAT','UNKNOWN')
    out.append(dict(name='essential_exception',expected=False,result=result))
    # Two genuinely repeated source phases; whole word is fixed for the oracle.
    base=Instance(((1,2),(0,-1),(4,3),(-1,2),(-1,-1)),frozenset({4}))
    for i in range(6):
        G=frozenset((p,rng.choice([q for q in range(4) if q!=p])) for p in range(4))
        I=replace(base,flags=G);m,n=rng.randrange(3),rng.randrange(3)
        C=Compiler(I);f,meta=C.scheme([Phase(0,(0,1)),Phase(2,(2,3))])
        extra=[Eq(meta['entry'],literal('')),Eq(meta['bridges'][0],literal('1')),Eq(meta['bridges'][1],literal('0')),
               Eq(meta['powers'][0],literal('00'*m)),Eq(meta['powers'][1],literal('11'*n))]
        for B,segments in meta['bases']:
            bit='0' if B==meta['bases'][0][0] else '1'
            extra += [Eq(B,literal(bit*2))]+[Eq(s,literal(bit)) for s in segments]
        w='00'*m+'1'+'11'*n+'0';expected=witness(I,w)
        result=run_script(C.script(f,extra,timeout_ms=750),[meta['word']],wall_seconds=3)
        assert result['status']=='UNKNOWN' or (result['status']=='SAT')==expected,(m,n,G,result)
        if result['status']=='SAT':assert result['values'][meta['word']]==w and border_witness(I,w)
        out.append(dict(name='two_cycle_'+str(i),word=w,expected=expected,result=result))
    # A mixed one-phase family with exact language 0^m100, valid iff m<2.
    # Grounded cases exercise full formula reconstruction, not just the local lemma.
    small=Instance(((0,1),(2,-1),(3,-1),(-1,-1)),frozenset({3}),frozenset({(0,1)}))
    for mode in (0,1,2,'positive','two_or_more'):
        C=Compiler(small);f,meta=C.scheme([Phase(0,(0,))]);B,segments=meta['bases'][0]
        extra=[Eq(meta['entry'],literal('')),Eq(meta['bridges'][0],literal('100')),
               Eq(B,literal('0')),Eq(segments[0],literal('0'))]
        if isinstance(mode,int):
            extra.append(Eq(meta['powers'][0],literal('0'*mode)))
        elif mode=='positive':
            extra.append(C.nonempty(meta['powers'][0]))
        else:
            from shared_word_templates import cat,lit,star
            extra.append(C.mem(meta['powers'][0],cat(lit('00'),star(lit('0')))))
        expected=mode in (0,1,'positive')
        result=run_script(C.script(f,extra,timeout_ms=1500),[meta['word'],meta['powers'][0]],wall_seconds=4)
        assert result['status']=='UNKNOWN' or (result['status']=='SAT')==expected,(mode,result)
        if result['status']=='SAT':
            w=result['values'][meta['word']]
            assert witness(small,w) and border_witness(small,w)
            assert w==result['values'][meta['powers'][0]]+'100'
        out.append(dict(name='small_full_scheme_'+str(mode),expected=expected,result=result))
    stats={s:sum(x['result']['status']==s for x in out) for s in ('SAT','UNSAT','UNKNOWN')}
    return dict(status='PASS',counts=stats,probes=out,
                caveat='Incomplete optional string backend, UNKNOWN retained; UNSAT is not independently proof checked')


if __name__=='__main__':
    result=optional_smt() if '--with-smt' in sys.argv else core()
    path=ROOT/'results'/('source-power-smt.json' if '--with-smt' in sys.argv else 'source-power.json')
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k in ('status','counts','exceptional_fixture')},indent=2))
