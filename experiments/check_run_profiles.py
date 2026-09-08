"""E036: all-instance arithmetic profile normalization and last-bit slices.

Finite checks support the implementation. The universal conclusions rest on
notes/2026-09-06-run-profile-normalization.md, not on bounded search success.
"""
from dataclasses import replace
from itertools import product
from math import factorial
from pathlib import Path
import hashlib
import json
import random

from border_lab import Instance, words, witness, border_witness
from run_profiles import (unary_orbit, compress_lengths, pair_signature,
                          equal_tail_pairs, numeric_profile, split_runs, join_runs,
                          normalize_candidate, last_bit_slice, run_length_bound,
                          encode_zero_tail,decode_zero_tail,bounded_run_encoding,
                          final_symbol_frontier_decision)

ROOT = Path(__file__).resolve().parents[1]


def direct_profile(I,w):
    """Literal forward definition, independent of unary orbits and block guards."""
    c=I.run(w)
    if c is None or c[-1] not in I.final:
        return None
    out=set()
    for j in range(len(w)+1):
        tail=w[j:]
        for i in range(j+1):
            if w.startswith(tail,i):
                out.add((c[i],c[j]))
    return frozenset(out)


def reverse_profile(I,w):
    c=I.run(w)
    if c is None or c[-1] not in I.final:return None
    rho,cs=w[::-1],c[::-1]
    return frozenset((cs[m],cs[b]) for m in range(len(w)+1)
                     for b in range(m+1) if rho[:b]==rho[m-b:m])


def unary_checks(counts):
    """Exhaust all partial unary functions on one, two and three states."""
    for k in (1,2,3):
        for tr in product(range(-1,k),repeat=k):
            I=Instance(tuple((-1,t) for t in tr),frozenset(range(k)))
            O=unary_orbit(I,'0')
            N=O.cutoff+2*O.difference_cutoff+2*O.period
            paths=[]
            for p in range(k+1):
                seq=[p]
                for _ in range(N):seq.append(O.table[seq[-1]])
                paths.append(seq)
                for n in range(N+1):
                    assert O.at(p,n)==seq[n]
                    counts['unary_state_checks']+=1
            types={}
            for n,m in product(range(N+1),repeat=2):
                signature=pair_signature(n,m,O)
                aggregate=[]
                for p,q in product(range(k),repeat=2):
                    expected=frozenset((paths[p][n-t],paths[q][m-t]) for t in range(min(n,m)+1))
                    assert equal_tail_pairs(O,p,n,q,m)==expected
                    aggregate.append(expected)
                    counts['tail_orbit_checks']+=1
                if signature in types:assert types[signature]==tuple(aggregate)
                else:types[signature]=tuple(aggregate)
            counts['unary_functions']+=1


def small_words(counts):
    for tr in product(range(-1,2),repeat=4):
        I=Instance((tr[:2],tr[2:]),frozenset({0,1}))
        for w in words('01',7):
            c=I.run(w)
            if c is None:continue
            old=direct_profile(I,w)
            assert old==reverse_profile(I,w)
            out=normalize_candidate(I,w)
            assert direct_profile(I,out['word'])==old
            assert set(I.run(out['word']))==set(c)
            if w:
                num=numeric_profile(I,split_runs(w,w[-1]),w[-1])
                assert num['profile']==old
                counts['numeric_raw_comparisons']+=1
            counts['two_state_defined_words']+=1


def accepted_long_runs(rng,counts):
    examples=[]
    for case in range(240):
        k=rng.randrange(3,10)
        marker=rng.choice('01')
        data=1-int(marker)
        perm=list(range(k-1));rng.shuffle(perm)
        # Complete unary permutations plus independently chosen marker edges.
        marker_edges=[rng.randrange(k) for _ in range(k-1)]
        marker_edges[rng.randrange(k-1)]=k-1
        rows=[]
        for p in range(k-1):
            row=[-1,-1];row[data]=perm[p];row[int(marker)]=marker_edges[p];rows.append(tuple(row))
        I=Instance(tuple(rows)+((-1,-1),),frozenset({k-1}))
        O=unary_orbit(I,marker)
        lengths=[];q=I.start
        desired=rng.randrange(1,7)
        for stage in range(desired):
            acceptable=[]
            for n in range(180,420):
                end=O.at(q,n);target=I.delta[end][int(marker)]
                if (stage+1==desired)==(target==k-1):acceptable.append((n,target))
            if not acceptable:break
            n,q=rng.choice(acceptable);lengths.append(n)
        if len(lengths)!=desired or q!=k-1:continue
        w=join_runs(lengths,marker)
        before=direct_profile(I,w)
        out=normalize_candidate(I,w)
        v=out['word']
        assert direct_profile(I,v)==before
        assert numeric_profile(I,lengths,marker)['profile']==before
        assert set(I.run(v))==set(I.run(w))
        counts['long_accepted_candidates']+=1
        counts['numeric_raw_comparisons']+=1
        counts['removed_letters']+=len(w)-len(v)
        if w!=v:counts['strict_contractions']+=1
        for _ in range(4):
            G=frozenset((p,q) for p in range(k) for q in range(k) if rng.random()<.08)
            bad=frozenset(p for p in range(k) if rng.random()<.025)
            J=replace(I,flags=G,bad=bad)
            assert witness(J,w)==witness(J,v)==border_witness(J,v)
            counts['annotation_checks']+=1
        if len(examples)<4 and len(w)>len(v):
            examples.append(dict(states=k,marker=marker,period=O.period,
                                 old_lengths=lengths,new_lengths=out['lengths'],
                                 original_length=len(w),normalized_length=len(v),
                                 unique_agreement_pairs=len(before)))
    return examples


def huge_integer_checks(rng,counts):
    for k in range(2,10):
        for _ in range(80):
            rows=tuple(tuple(rng.randrange(-1,k) for _ in (0,1)) for p in range(k))
            I=Instance(rows,frozenset(range(k)),start=rng.randrange(k))
            marker=rng.choice('01');O=unary_orbit(I,marker)
            base=10**30+rng.randrange(1000)
            lengths=tuple(rng.choice((rng.randrange(O.cutoff+1),
                         base+rng.randrange(3*O.difference_cutoff),
                         2*base+rng.randrange(1000))) for _ in range(rng.randrange(1,10)))
            small=compress_lengths(lengths,O)
            for i in range(len(lengths)):
                for j in range(len(lengths)):
                    assert pair_signature(lengths[i],lengths[j],O)==pair_signature(small[i],small[j],O)
                    p,q=rng.randrange(k),rng.randrange(k)
                    assert equal_tail_pairs(O,p,lengths[i],q,lengths[j])==equal_tail_pairs(O,p,small[i],q,small[j])
                    counts['huge_integer_pair_checks']+=1
            assert numeric_profile(I,lengths,marker)==numeric_profile(I,small,marker)
            counts['huge_integer_vectors']+=1


def last_bit_checks(rng,counts):
    for _ in range(200):
        k=rng.randrange(2,8)
        finals=frozenset(q for q in range(k) if rng.random()<.25)
        rows=tuple((-1,-1) if q in finals else tuple(rng.randrange(-1,k) for a in (0,1)) for q in range(k))
        flags=frozenset((p,q) for p in range(k) for q in range(k) if rng.random()<.07)
        bad=frozenset(q for q in range(k) if rng.random()<.03)
        I=Instance(rows,finals,flags,bad,rng.randrange(k))
        slices={(f,a):last_bit_slice(I,f,a) for f in finals for a in '01'}
        for w in words('01',7):
            if not w:continue
            orig=witness(I,w)
            lifted=any(witness(J,w) for J in slices.values())
            assert orig==lifted
            c=I.run(w)
            for (f,a),J in slices.items():
                expected=c is not None and c[-1]==f and w[-1]==a
                assert J.admissible(w)==(expected and not set(c)&bad)
            counts['last_bit_word_checks']+=1
        counts['last_bit_instances']+=1


def fixture_checks(counts):
    # Weak order and residues alone do not preserve transient gap information.
    I=Instance(((-1,1),(-1,2),(3,2),(-1,4),(5,4),(-1,-1)),
               frozenset({5}),frozenset({(1,3)}))
    a,b=join_runs((101,100),'0'),join_runs((102,100),'0')
    assert not witness(I,a) and witness(I,b)
    O=unary_orbit(I,'0');assert O.period==1
    assert min(100,101)>O.cutoff
    assert (1,3) in direct_profile(I,a) and (1,3) not in direct_profile(I,b)
    # Huge actual unary exponents, evaluated without materializing either word.
    old=(10**30+2,10**30)
    small=compress_lengths(old,O)
    pa=numeric_profile(I,old,'0');pb=numeric_profile(I,small,'0')
    assert pa==pb and not pa['profile'] & I.flags
    v=join_runs(small,'0');assert witness(I,v) and border_witness(I,v)
    # A target lies on a productive marker cycle, outside C056's certificate.
    J=Instance(((1,0),(2,1),(3,0),(-1,-1)),frozenset({3}),frozenset({(0,1)}))
    ls=(401,307,401,307,0)
    w=join_runs(ls,'0');assert witness(J,w)
    out=normalize_candidate(J,w)
    assert direct_profile(J,w)==direct_profile(J,out['word'])
    assert witness(J,out['word']) and border_witness(J,out['word'])
    from target_frontier import parse_macro,frontier_structure
    cert,macro=parse_macro(J,3,code='unary')
    assert cert['status']=='FORMATTED'
    structure,_=frontier_structure(macro)
    assert structure['status']=='NOT_APPLICABLE'
    # Last-bit slicing resolves a format rejection without adding any marker.
    K=Instance(((1,-1),(-1,2),(-1,-1)),frozenset({2}))
    from marker_certificate import marker_decision
    assert marker_decision(K)['status']=='UNKNOWN'
    # Relabel the bits globally in the 1-ending slice, not at selected positions.
    Q=last_bit_slice(K,2,'1')
    Q=replace(Q,delta=tuple((row[1],row[0]) for row in Q.delta))
    improved=marker_decision(Q)
    assert improved['status']=='YES' and improved['word']=='10'
    counts['guard_fixtures']+=3
    return dict(short_gap_guard=dict(period=1,cutoff=O.cutoff,first_lengths=(101,100),
                                     second_lengths=(102,100),changed_pair=(1,3)),
                huge_witness=dict(original_lengths=old,normalized_lengths=small,
                                  word=v,agreement_pairs=sorted(pb['profile'])),
                recurrent_target=dict(delta=J.delta,flags=sorted(J.flags),
                                      old_lengths=ls,new_lengths=out['lengths'],
                                      previous_certificate=structure,
                                      old_length=len(w),new_length=len(out['word'])),
                final_bit_slice=dict(original_word='01',relabeled_word=improved['word']))


def encoding_checks(rng,counts):
    for _ in range(160):
        k=rng.randrange(1,7)
        finals=frozenset(q for q in range(k) if rng.random()<.4)
        terminal=rng.choice((False,True))
        table=tuple((-1,-1) if terminal and q in finals else tuple(rng.randrange(-1,k) for _ in (0,1)) for q in range(k))
        G=frozenset((p,q) for p in range(k) for q in range(k) if rng.random()<.13)
        B=frozenset(q for q in range(k) if rng.random()<.05)
        I=Instance(table,finals,G,B,rng.randrange(k))
        J=bounded_run_encoding(I)
        assert len(J.delta)==2*k and J.flags==I.flags and J.bad==I.bad
        for w in words('01',6):
            ew=encode_zero_tail(w)
            assert decode_zero_tail(ew)==w
            assert '11' not in ew and (not ew or ew.endswith('0'))
            assert witness(I,w)==witness(J,ew)==border_witness(J,ew)
            if I.admissible(w):
                old=direct_profile(I,w);new=direct_profile(J,ew)
                assert old==frozenset((p,q) for p,q in new if p<k and q<k)
            counts['encoding_forward_checks']+=1
        for ew in words('01',8):
            w=decode_zero_tail(ew)
            assert J.admissible(ew)==(w is not None and I.admissible(w))
            counts['encoding_raw_checks']+=1
    # All zero-tail encoding blocks are length zero or one, but express full I.
    I=Instance(((2,1),(2,1),(-1,3),(4,3),(-1,-1)),frozenset({4}),
               frozenset({(0,2),(0,3),(1,2)}))
    J=bounded_run_encoding(I)
    for n in range(12):
        w='1'*n+'0'+'1'*(n+1)+'0';z=encode_zero_tail(w)
        assert max(split_runs(z,'0'))<=1
        assert not witness(J,z)
        counts['hard_normal_form_checks']+=1
    from terminal_realization import realize
    from denial_bridge import Canonical
    # Exact regular-model checks for two small terminal fixtures, both forms.
    for I, candidates in ((Instance(((1,-1),(2,-1),(-1,-1)),frozenset({2}),frozenset({(0,1)})),('00',)),
                          (Instance(((1,-1),(-1,2),(-1,-1)),frozenset({2})),('01',))):
        for M,ws in ((I,candidates),(bounded_run_encoding(I),tuple(encode_zero_tail(w) for w in candidates))):
            R=realize(M)
            for w in ws:
                assert (not Canonical(R.variables,R.constraints,R.alpha,R.beta,w).errors())==witness(M,w)
                counts['canonical_path_checks']+=1


def wrapper_checks(rng,counts):
    from target_frontier import Limits,target_frontier_decision
    limits=Limits(states=10000,transitions=100000,descriptors=10000,schemas=1000,reconstruction=10000)
    totals=dict(YES=0,NO=0,UNKNOWN=0)
    for _ in range(160):
        k=rng.randrange(2,7)
        # Acyclic raw graphs: enumerate every accepted word through k-1.
        D=tuple(tuple(rng.choice([-1]+list(range(q+1,k))) for _ in (0,1)) for q in range(k))
        finals=frozenset(q for q,row in enumerate(D) if row==(-1,-1) and rng.random()<.8)
        G=frozenset((p,q) for p in range(k) for q in range(k) if rng.random()<.06)
        I=Instance(D,finals,G)
        expected=any(witness(I,w) for w in words('01',k-1))
        result=final_symbol_frontier_decision(I,limits)
        assert result['status']!='UNKNOWN' and (result['status']=='YES')==expected
        totals[result['status']]+=1;counts['wrapper_complete_oracles']+=1
    I=Instance(((1,-1),(-1,2),(-1,-1)),frozenset({2}))
    assert target_frontier_decision(I,limits)['status']=='UNKNOWN'
    out=final_symbol_frontier_decision(I,limits)
    assert out['status']=='YES' and out['word']=='01'
    # The new wrapper is not advertised as resolving recurrent targets.
    J=Instance(((1,0),(2,1),(3,0),(-1,-1)),frozenset({3}),frozenset({(0,1)}))
    assert final_symbol_frontier_decision(J,limits)['status']=='UNKNOWN'
    return totals


def main():
    rng=random.Random(2026090657)
    counts=dict(unary_functions=0,unary_state_checks=0,tail_orbit_checks=0,
                two_state_defined_words=0,numeric_raw_comparisons=0,
                long_accepted_candidates=0,strict_contractions=0,removed_letters=0,
                annotation_checks=0,huge_integer_pair_checks=0,huge_integer_vectors=0,
                last_bit_instances=0,last_bit_word_checks=0,guard_fixtures=0,
                encoding_forward_checks=0,encoding_raw_checks=0,hard_normal_form_checks=0,
                canonical_path_checks=0,wrapper_complete_oracles=0)
    unary_checks(counts)
    small_words(counts)
    examples=accepted_long_runs(rng,counts)
    huge_integer_checks(rng,counts)
    last_bit_checks(rng,counts)
    fixtures=fixture_checks(counts)
    encoding_checks(rng,counts)
    wrapper_oracles=wrapper_checks(rng,counts)
    def blob(p):
        raw=(ROOT/'experiments'/p).read_bytes()
        return hashlib.sha1(('blob %d\0'%len(raw)).encode()+raw).hexdigest()
    out=dict(status='PASS',seed=2026090657,counts=counts,examples=examples,fixtures=fixtures,wrapper_oracles=wrapper_oracles,
             dependency_blobs={p:blob(p) for p in ('border_lab.py','target_frontier.py','marker_certificate.py')},
             proof_status='Written all-instance proofs, not Lean-checked or independently reviewed',
             limit='No computable bound on the number of occurrences of the final symbol is proved')
    (ROOT/'results'/'run-profiles.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
