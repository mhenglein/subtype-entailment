"""Deterministic adversarial checks for flag transport and separator-tail search.

Proofs and all-length counterexample:
notes/2026-09-08-flag-transport-and-separator-obstruction.md.
Finite tests are evidence for implementation, not an unrestricted theorem.
"""
import hashlib
import itertools
import json
import random
from collections import Counter, deque
from pathlib import Path

from border_lab import Instance,witness,border_witness,words
from lastflag_spectrum import boundary_slice,realize_template,is_lastflag,ActionMonoid
from flag_transport import (transport_edges,verify_transport,relocate,relocation_orbits,
                            synchronous_colouring,verify_colouring,compile_logical,
                            encode_logical,decode_logical,best_relocation,
                            transport_tail_decision,nine_state_obstruction,obstruction_word,
                            eleven_state_nonflat_obstruction)
from separator_tail import (Limits,tail_safe,relaxed_decision,semantic_decision,
                            spectrum_slice,_weighted_fibres,_source_step,_observe,
                            _observations,_recover)

ROOT=Path(__file__).resolve().parents[1]
SEED=2026090881
LIMITS=Limits(states=30000,steps=300000,descriptors=30000,schemas=30000,
              blocks=6,monoid=10000,combinations=3000000)


def flagged_cuts(I,w,flags=None):
    """Literal substring equality rather than the production startswith loop."""
    c=I.run(w)
    if c is None or not I.admissible(w):return ()
    G=I.flags if flags is None else flags
    n=len(w)
    return tuple((i,j) for j in range(n+1) for i in range(j+1)
                 if (c[i],c[j]) in G and w[i:i+n-j]==w[j:])


def tail_oracle(I,w,marker,H):
    if not I.admissible(w):return False
    c=I.run(w);n=len(w)
    if any((p,p) in I.flags or (p,c[-1]) in I.flags for p in c):return False
    rho=w[::-1];rc=c[::-1]
    for length in range(1,n+1):
        for border in range(1,length):
            if rho[:border]==rho[length-border:length] and (rc[length],rc[border]) in I.flags:
                if rho[:border].count(marker)<=H:return False
    return True


def all_dag_words(I):
    """Complete oracle for strictly increasing state transitions, no cutoff."""
    for p,row in enumerate(I.delta):
        assert all(q<0 or q>p for q in row)
    todo=[(I.start,'')];out=[]
    while todo:
        p,w=todo.pop()
        if p in I.final:out.append(w)
        for a,q in zip(I.alphabet,I.delta[p]):
            if q>=0:todo.append((q,w+a))
    return out


def code_check(I,w,marked):
    J=compile_logical(I,marked);u=encode_logical(I,w,marked)
    assert decode_logical(I,u,marked)==w
    assert witness(I,w)==witness(J,u)==border_witness(J,u)
    c=I.run(w)
    offsets=[0]
    for i,a in enumerate(w):offsets.append(offsets[-1]+1+int((c[i],int(a)) in marked))
    left={(offsets[i],offsets[j]) for i,j in flagged_cuts(I,w)}
    assert left==set(flagged_cuts(J,u))
    return J,u


def exhaustive_transport():
    counts=Counter();randomizer=random.Random(SEED)
    for k in range(1,4):
        for raw in itertools.product(range(-1,k),repeat=2*(k-1)):
            table=tuple(tuple(raw[2*p:2*p+2]) for p in range(k-1))+((-1,-1),)
            plain=Instance(table,frozenset({k-1}))
            accepted=[w for w in words('01',7) if plain.admissible(w)]
            local=transport_edges(plain)
            counts['tables']+=1
            for g,h,a in local:
                assert verify_transport(plain,g,h,a)
                for w in accepted:
                    # Extra unrelated flags and Bad annotations cannot repair a false equivalence.
                    assert bool(flagged_cuts(plain,w,{g}))==bool(flagged_cuts(plain,w,{h}))
                    counts['local_equivalence_words']+=1
                counts['local_proof_edges']+=1
            possible=[(p,q) for p in range(k-1) for q in range(k-1) if p!=q]
            for bits in range(1<<len(possible)):
                G=frozenset(g for j,g in enumerate(possible) if bits>>j&1)
                I=Instance(table,plain.final,G)
                report,J=best_relocation(I,None)
                assert report['status']=='OPTIMAL_IN_TRANSPORT_ORBIT'
                marked=synchronous_colouring(I)
                assert verify_colouring(I,marked)
                for w in accepted:
                    assert witness(I,w)==witness(J,w)==border_witness(J,w)
                    code_check(I,w,marked)
                    counts['annotation_word_checks']+=1
                counts['normalized_instances']+=1
    # Larger random tables provide substantially more nontrivial reverse transports.
    for case in range(160):
        k=randomizer.randrange(3,8)
        table=tuple(tuple(-1 if randomizer.random()<.3 else randomizer.randrange(k)
                          for _ in range(2)) for p in range(k-1))+((-1,-1),)
        I=Instance(table,frozenset({k-1}),
                   frozenset((p,q) for p in range(k) for q in range(k) if randomizer.random()<.13),
                   frozenset(p for p in range(k) if randomizer.random()<.05),
                   randomizer.randrange(k))
        report,J=best_relocation(I,10000)
        assert report['status']=='OPTIMAL_IN_TRANSPORT_ORBIT'
        for w in words('01',7):
            assert witness(I,w)==witness(J,w)==border_witness(J,w)
            counts['random_annotation_words']+=1
            if I.run(w) is not None:
                code_check(I,w,synchronous_colouring(I));counts['random_code_words']+=1
        counts['random_instances']+=1
    return dict(counts)


def dag_oracles():
    rng=random.Random(SEED+1);counts=Counter()
    for case in range(220):
        k=rng.randrange(2,8)
        finals=frozenset(p for p in range(k) if p==k-1 or rng.random()<.12)
        table=[]
        for p in range(k):
            row=[]
            for a in '01#':
                opts=[q for q in range(p+1,k) if q not in finals or a=='#']
                row.append(rng.choice(opts) if p not in finals and opts and rng.random()<.66 else -1)
            table.append(tuple(row))
        I=Instance(tuple(table),finals,
                   frozenset((p,q) for p in range(k) for q in range(k) if rng.random()<.08),
                   frozenset(p for p in range(k) if rng.random()<.035),
                   0,'01#')
        candidates=all_dag_words(I)
        counts['complete_accepted_words']+=len(candidates)
        for H in range(4):
            good=[w for w in candidates if tail_oracle(I,w,'#',H)]
            for w in candidates:
                assert tail_safe(I,w,'#',H)==tail_oracle(I,w,'#',H)
                counts['predicate_comparisons']+=1
            answer=relaxed_decision(I,'#',H,LIMITS)
            assert answer['status']==('YES' if good else 'NO'),(case,H,answer)
            if good:assert answer['word'] in good
            counts['relaxation_queries']+=1;counts[answer['status']]+=1
        actual=any(witness(I,w) for w in candidates)
        answer=semantic_decision(I,'#',LIMITS)
        assert answer['status']==('YES' if actual else 'NO'),(case,answer)
        if actual:assert witness(I,answer['word'])
        counts['semantic_decisions']+=1
        for f in sorted(I.final):
            sliced=boundary_slice(I,f)
            if sliced is None:continue
            J,_=sliced
            spectrum=spectrum_slice(J,'#',LIMITS)
            assert spectrum['status']=='FINITE'
            maximum=0
            for w in all_dag_words(J):
                for i,j in flagged_cuts(J,w):
                    if i<j<len(w) and is_lastflag(J,w,i,j):
                        maximum=max(maximum,w[j:].count('#'))
            assert spectrum['H']==maximum
            counts['complete_spectrum_checks']+=1
    return dict(counts)


def obstruction_checks():
    I=nine_state_obstruction();counts=Counter()
    marked=synchronous_colouring(I)
    assert marked==frozenset({(5,0),(6,0),(7,0),(8,0)})
    K=compile_logical(I,marked)
    for n in range(33):
        for m in range(1,33):
            w=obstruction_word(n,m);cuts=flagged_cuts(I,w);c=I.run(w)
            expected={(0,3)} if n<m else {(0,2)} if n==m else {(5,6)}
            assert {(c[i],c[j]) for i,j in cuts}==expected
            assert len(cuts)==1
            selected=(0,2*(m+1)) if n<m else (0,2*(n+1)) if n==m else (2*(n-m)-1,2*n+1)
            assert cuts==(selected,)
            assert not witness(I,w) and not border_witness(I,w)
            counts['parameter_words']+=1
    for w in words('01',16):
        counts['binary_words']+=1
        if not I.admissible(w):continue
        # Exact candidate-language parsing independently of the transition path.
        assert len(w)%2==0
        tokens=[w[i:i+2] for i in range(0,len(w),2)]
        assert all(t in ('00','10') for t in tokens)
        decoded=''.join(t[0] for t in tokens)
        middle=decoded.split('0')
        assert len(middle)==3 and middle[-1]==''
        n,m=len(middle[0]),len(middle[1])
        assert w==obstruction_word(n,m)
        assert flagged_cuts(I,w) and not witness(I,w)
        code_check(I,w,marked)
        counts['accepted_binary_words']+=1
    essentials=[]
    for flag,n,m in [((0,3),0,1),((0,2),1,1),((5,6),2,1)]:
        J=Instance(I.delta,I.final,I.flags-{flag})
        w=obstruction_word(n,m)
        assert witness(J,w) and border_witness(J,w)
        essentials.append(dict(removed=flag,word=w))
    # A single REAL violation forces the entire mandatory transition class.
    w=obstruction_word(2,1);c=I.run(w);i,j=flagged_cuts(I,w)[0]
    assert (i,j)==(1,5)
    pairs=[(c[i+t],c[j+t]) for t in range(len(w)-j+1)]
    assert pairs==[(5,6),(1,2),(5,7),(1,3),(6,8),(2,4)]
    all_edges=[(p,a) for p,row in enumerate(I.delta) for a,q in enumerate(row) if q>=0]
    valid_colours=0;forcing_compatible_colours=0
    forcing_word=obstruction_word(2,1);forcing_trace=I.run(forcing_word)
    for bits in range(1<<len(all_edges)):
        color=frozenset(e for index,e in enumerate(all_edges) if bits>>index&1)
        if verify_colouring(I,color):
            valid_colours+=1;assert marked<=color
        if (8,0) in color:
            encoded=encode_logical(I,forcing_word,color)
            offsets=[0]
            for t,a in enumerate(forcing_word):
                offsets.append(offsets[-1]+1+int((forcing_trace[t],int(a)) in color))
            if encoded[offsets[1]:].startswith(encoded[offsets[5]:]):
                forcing_compatible_colours+=1;assert marked<=color
    # Escape family has unique violation and exact minimum-colouring cost n+1.
    for n in range(25):
        w=obstruction_word(n,n+1);logical=encode_logical(I,w,marked)
        cuts=flagged_cuts(K,logical);assert len(cuts)==1
        i,j=cuts[0];assert logical[j:].count('#')==n+1
        for H in range(12):
            assert tail_oracle(K,logical,'#',H)==(n+1>H)
            assert tail_safe(K,logical,'#',H)==(n+1>H)
            counts['escape_tail_identities']+=1
    report,J=best_relocation(I,None)
    assert J.flags==frozenset({(0,2),(0,3),(1,2)})
    assert synchronous_colouring(J)==frozenset({(6,0),(8,0)})
    original=semantic_decision(K,'#',LIMITS)
    assert original['status']=='UNKNOWN'
    assert original['slices'][0]['analysis']['status']=='UNBOUNDED'
    cert=original['slices'][0]['analysis']['pumping_certificate']
    norm,_=boundary_slice(K,4)
    for m in range(1,16):assert is_lastflag(norm,**realize_template(cert,m))
    fixed=compile_logical(J,synchronous_colouring(J))
    repaired=semantic_decision(fixed,'#',LIMITS)
    assert repaired['status']=='NO' and repaired['slices'][0]['analysis']['H']==1
    direct=transport_tail_decision(I,1,limits=LIMITS)
    assert direct['status']=='NO'
    raw_results=[]
    for H in range(5):
        result=relaxed_decision(K,'#',H,LIMITS)
        assert result['status']=='YES' and not result['actual_witness']
        raw_results.append(dict(H=H,word=result['word']))
    return dict(counts,essential_flags=essentials,forcing_word=obstruction_word(2,1),
                forcing_pairs=pairs,valid_colourings=valid_colours,
                forcing_word_compatible_colourings=forcing_compatible_colours,relocation=report,
                original_semantic=original,repaired_semantic=repaired,tail_survivors=raw_results)



def nonflat_checks():
    I=eleven_state_nonflat_obstruction();counts=Counter()
    mark=synchronous_colouring(I)
    assert mark==frozenset((p,0) for p in range(6,11))
    K=compile_logical(I,mark)
    # Decode even-position tokens to the original six-state reset automaton.
    old=Instance(((2,1),(2,1),(2,3),(2,4),(5,3),(-1,-1)),frozenset({5}),
                 frozenset({(0,2),(0,3),(0,4),(1,2)}))
    for w in words('01',12):
        if not old.admissible(w):continue
        encoded=''.join(a+'0' for a in w)
        assert I.admissible(encoded) and not witness(old,w)
        assert witness(I,encoded)==witness(old,w)==border_witness(I,encoded)
        counts['reset_language_words']+=1
    for n in range(21):
        for m in range(2,22,2):
            w=obstruction_word(n,m)
            assert I.admissible(w) and len(flagged_cuts(I,w))==1
            counts['two_block_words']+=1
    for n in range(1,32,2):
        w=obstruction_word(n,n+1);logical=encode_logical(I,w,mark)
        cuts=flagged_cuts(K,logical);assert len(cuts)==1
        i,j=cuts[0];assert logical[j:].count('#')==n+1
        for H in range(12):
            assert tail_safe(K,logical,'#',H)==tail_oracle(K,logical,'#',H)==(n+1>H)
            counts['nonflat_escape_identities']+=1
    essential=[]
    for flag,n,m in [((0,4),0,2),((0,3),1,2),((0,2),2,2),((6,7),3,2)]:
        X=Instance(I.delta,I.final,I.flags-{flag});w=obstruction_word(n,m)
        assert witness(X,w) and border_witness(X,w)
        essential.append(dict(removed=flag,word=w))
    forcing=obstruction_word(3,2);i,j=flagged_cuts(I,forcing)[0];c=I.run(forcing)
    path=[(c[i+t],c[j+t]) for t in range(len(forcing)-j+1)]
    assert path==[(6,7),(1,2),(6,8),(1,3),(6,9),(1,4),(7,10),(2,5)]
    report,J=best_relocation(I,None)
    assert J.flags==old.flags and set(report['marked'])=={(7,0),(10,0)}
    original=semantic_decision(K,'#',LIMITS)
    assert original['status']=='UNKNOWN' and original['slices'][0]['analysis']['status']=='UNBOUNDED'
    repaired=semantic_decision(compile_logical(J,synchronous_colouring(J)),'#',LIMITS)
    assert repaired['status']=='NO' and repaired['slices'][0]['analysis']['H']==1
    assert transport_tail_decision(I,limits=LIMITS)['status']=='NO'
    # Removing only the equality-case flag leaves an infinite positive language.
    # Both placements still define exactly the same nonempty witness language.
    P=Instance(I.delta,I.final,I.flags-{(0,2)})
    positive=transport_tail_decision(P,limits=LIMITS)
    assert positive['status']=='YES' and witness(P,positive['word'])
    for n in range(2,22,2):
        assert witness(P,obstruction_word(n,n))
        counts['positive_family_words']+=1
    return dict(counts,forcing_word=forcing,forcing_cuts=[i,j],forcing_pair_path=path,
                essential_flags=essential,relocation=report,original_semantic=original,
                repaired_semantic=repaired,positive_companion=positive)


def cyclic_oracles():
    """Infinite arbitrary-data cases with directly proved language formulas."""
    counts=Counter();rows=[]
    # Raw three-state fixture retained UNKNOWN by the old target-cone wrapper.
    I=Instance(((1,0),(0,2),(-1,-1)),frozenset({2}),frozenset({(0,1)}))
    answer=transport_tail_decision(I,1,limits=LIMITS)
    assert answer['status']=='YES' and answer['word']=='01'
    rows.append(dict(name='target_recurrent_main_fixture',answer=answer))
    # A data loop over TWO letters. Both flag-free words and boundary-refuted
    # variants are infinite, but truth follows without testing a finite cutoff.
    for flags in [frozenset(),frozenset({(0,1)}),frozenset({(1,0)})]:
        K=Instance(((0,0,1),(-1,-1,-1)),frozenset({1}),flags,alphabet='01#')
        for H in (0,1,2,3):
            a=relaxed_decision(K,'#',H,LIMITS)
            assert a['status']==('NO' if (0,1) in flags else 'YES')
            counts['infinite_two_data_queries']+=1
    # Nonflat arbitrary data, exactly two # blocks: no flags, one equality-hit
    # flag. Initial state is visited throughout block 1, target throughout block 2.
    # G(0,1) makes every candidate bad: target '#', earlier '#' always agrees.
    K=Instance(((0,0,1),(1,1,2),(-1,-1,-1)),frozenset({2}),
               frozenset({(0,1)}),alphabet='01#')
    for H in (1,2,3):
        a=relaxed_decision(K,'#',H,LIMITS);assert a['status']=='NO'
        counts['infinite_two_data_queries']+=1
    # New source-replay path can exceed every reference length. Separate source
    # chain followed by a short reference with no source/reference equalities.
    K=Instance(((1,2,-1),(1,2,-1),(2,2,3),(3,3,4),(-1,-1,-1)),
               frozenset({4}),alphabet='01#')
    for H in (1,2,3):
        a=relaxed_decision(K,'#',H,LIMITS)
        assert a['status']=='YES' and witness(K,a['word'])
        counts['infinite_two_data_queries']+=1
    return dict(counts,fixtures=rows)


def weighted_graph_oracles():
    """Separate reachability/cycle and bounded DP check of weighted fibres."""
    rng=random.Random(SEED+2);counts=Counter()
    for case in range(200):
        n=rng.randrange(1,5)
        generators=[tuple(rng.randrange(n) for _ in range(n)) for _ in range(3)]
        mon=ActionMonoid.build(generators,'01#',5000)
        edges=mon.edges;N=len(edges)
        # Keep this independent oracle small; production monoid is already exact.
        if N>100:continue
        maximum,attain,cause,_=_weighted_fibres(edges,'01#','#')
        reachsets=[set() for _ in edges]
        for p in range(N):
            reached={p};todo=[p]
            for q in todo:
                for r in edges[q]:
                    if r not in reached:reached.add(r);todo.append(r)
            reachsets[p]=reached
        positive={p for p,row in enumerate(edges) if p in reachsets[row[2]]}
        infinity=set().union(*(reachsets[p] for p in positive)) if positive else set()
        values=[-1]*N;values[0]=0
        for _ in range(N):
            nxt=values[:]
            for p,row in enumerate(edges):
                if values[p]<0:continue
                for a,q in enumerate(row):nxt[q]=max(nxt[q],values[p]+int(a==2))
            values=nxt
        for p in range(N):
            assert (maximum[p] is None)==(p in infinity)
            if p not in infinity:
                assert maximum[p]==values[p]
                assert mon.action_index(attain[p])==p and attain[p].count('#')==maximum[p]
            counts['action_fibres']+=1
        counts['graphs']+=1
    return dict(counts)



def source_observation_oracles():
    """Literal source words vs common-reference descriptor saturation.

    For fixed reference length M, every observation has a representative of
    length <=M+k: longer unmatched prefixes carry no new equality/hit and
    shorten by simple reverse reachability. This is an exact finite oracle
    justified by that source-only bound, not a bound on full witness words.
    """
    rng=random.Random(SEED+3);counts=Counter()
    for case in range(100):
        k=rng.randrange(2,5)
        table=tuple(tuple(rng.choice([-1]+list(range(k))) for _ in range(3)) for _ in range(k))
        J=Instance(table,frozenset(),
                   frozenset((p,q) for p in range(k) for q in range(k) if rng.random()<.2),
                   alphabet='01#')
        pred=[[] for _ in range(k)]
        for p,row in enumerate(table):
            for ai,a in enumerate('01'):
                if row[ai]>=0:pred[row[ai]].append((a,p))
        candidates=[]
        for start in range(k):
            for w in words('01',3):
                tr=[start]
                for a in w:
                    if table[tr[-1]][int(a)]<0:break
                    tr.append(table[tr[-1]][int(a)])
                if len(tr)==len(w)+1 and table[tr[-1]][2]>=0:
                    candidates.append((start,tr[-1],table[tr[-1]][2],w,tr))
        if not candidates:counts['empty_generation_cases']+=1;continue
        selected=[rng.choice(candidates) for _ in range(rng.randrange(1,4))]
        schema=tuple(tuple(t[:3]) for t in selected)
        refs=tuple(t[3] for t in selected);traces=[t[4] for t in selected]
        r=len(refs);M=max(map(len,refs));eq=(1<<r)-1
        coords=tuple(t[-1] for t in traces)
        ends=[p for p,row in enumerate(table) if row[2]>=0]
        desc=frozenset((p,p,eq,_observe(p,eq,0,False,coords,J.flags),False) for p in ends)
        for depth in range(1,M+2):
            cols=tuple(w[-depth] if depth<=len(w) else '_' for w in refs)
            coords=tuple(t[len(t)-1-depth] if depth<len(t) else -1 for t in traces)
            desc=_source_step(desc,cols,coords,pred,J.flags)
        calculated=_observations(J,2,desc,pred);oracle=set()
        for start in range(k):
            for w in words('01',M+k):
                counts['literal_source_words']+=1
                tr=[start]
                for a in w:
                    if table[tr[-1]][int(a)]<0:break
                    tr.append(table[tr[-1]][int(a)])
                if len(tr)!=len(w)+1 or table[tr[-1]][2]<0:continue
                e=sum(1<<j for j,u in enumerate(refs) if w==u);h=0
                for j,u in enumerate(refs):
                    for t in range(min(len(u),len(w))+1):
                        if w[len(w)-t:]==u[len(u)-t:] and (tr[len(w)-t],traces[j][len(u)-t]) in J.flags:
                            h|=1<<j;break
                oracle.add((start,table[tr[-1]][2],e,h,tr[-1]))
        assert calculated==oracle,(case,refs,calculated-oracle,oracle-calculated)
        counts['exact_reference_sets']+=1
        for observation in sorted(calculated):
            _recover(J,2,schema,refs,observation,pred,LIMITS)
            counts['recovered_observations']+=1
    return dict(counts)


def guard_checks():
    counts=Counter()
    def raises(f):
        try:f()
        except ValueError:counts['invalid_input_rejections']+=1;return
        raise AssertionError('invalid input accepted')
    I=nine_state_obstruction()
    raises(lambda:relocate(I,(5,6),(1,3)))
    raises(lambda:compile_logical(I,[]))
    raises(lambda:best_relocation(I,0))
    raises(lambda:relaxed_decision(compile_logical(I,synchronous_colouring(I)),'#',-1))
    raises(lambda:Limits(states=0))
    assert best_relocation(I,1)[0]['status']=='UNKNOWN'
    K=compile_logical(I,synchronous_colouring(I))
    assert relaxed_decision(K,'#',2,Limits(blocks=1))['status']=='UNKNOWN'
    assert spectrum_slice(K,'#',Limits(monoid=1))['status']=='UNKNOWN'
    counts['capped_unknowns']=3
    necessary_guards=[
        ('incoming',((-1,1),(2,2),(-1,-1)),(0,1),(1,2),'1','10'),
        ('start',((-1,2),(-1,0),(-1,-1)),(1,0),(0,2),'1','1'),
        ('common',((0,1),(3,2),(-1,-1),(-1,-1)),(0,1),(1,2),'1','010'),
    ]
    for name,table,g,h,a,w in necessary_guards:
        P=Instance(table,frozenset({len(table)-1}),frozenset({g}))
        assert not verify_transport(P,g,h,a)
        assert bool(flagged_cuts(P,w,{g}))!=bool(flagged_cuts(P,w,{h}))
        counts['hypothesis_counterexamples']+=1
    # Positive-time pair inequality does not prohibit revisiting a pair.
    P=Instance(((0,1),(2,-1),(2,3),(-1,-1)),frozenset({3}),frozenset({(0,1)}))
    w='001001';c=P.run(w)
    assert P.admissible(w) and w[3:]=='001' and w.startswith(w[3:])
    orbit=[(c[t],c[3+t]) for t in range(4)]
    assert orbit[1]==orbit[2]==(0,2)
    assert all(p!=q for p,q in orbit)
    return dict(counts,nonmerging_repetition=dict(word=w,cuts=[0,3],pair_orbit=orbit))


def check():
    result=dict(seed=SEED,base='c4875e599958dd624dd7220dd7cbe5bb96822b11',
                proof_status='Written proof and independent algorithm checks; not Lean or human-refereed',
                scope='Exact flag relocation, finite separator relaxations, and all-H counterexample; not unrestricted Problem 1.7')
    for name,fn in [('transport',exhaustive_transport),('dag_oracles',dag_oracles),
                    ('obstruction',obstruction_checks),('nonflat',nonflat_checks),('cyclic',cyclic_oracles),
                    ('weighted',weighted_graph_oracles),('source_observations',source_observation_oracles),
                    ('guards',guard_checks)]:
        print('Checking',name,flush=True);result[name]=fn()
    result['status']='PASS'
    out=ROOT/'results/flag-transport.json'
    out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('obstruction','nonflat','cyclic')},indent=2))
    return result

if __name__=='__main__':check()
