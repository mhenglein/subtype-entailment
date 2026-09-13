#!/usr/bin/env python3
"""Independent all-cuts, window-automaton, and finite-NO-proof checks.

Finite tests are not a mathematical referee. NO is replayed only through a
complete, well-founded certificate tree. No bounded word scan supplies NO.
"""
from __future__ import annotations
from collections import Counter, deque
from itertools import product
from pathlib import Path
import argparse, copy, hashlib, json, random
from target_anchor import (Instance, FIXTURES as OLD_FIXTURES, normalize,
                           witness, reverse_witness, solve_with_tail_test,
                           solve_columns)
from target_return import (BASE, Domain, Limits, Capped, trim, return_certificate,
    fixed_tail_filter, filtered_spec, tail_patterns, last_columns_spec,
    domain_witness, solve, original_closed_columns, from_json)

SEED=20260913651
UNCAPPED=Limits(None,None,None,None)

FIXTURES={
 'legal_repeats':Instance(((2,-1),(4,0),(4,3),(1,2),(-1,-1)),0,frozenset({4}),
                        frozenset({(1,3),(2,1),(3,2)})),
 'recursive_no':Instance(((-1,4),(5,2),(0,5),(6,1),(3,7),(0,7),(7,4),(-1,-1)),
     0,frozenset({7}),frozenset({(0,1),(0,3),(0,4),(1,3),(1,4),(1,5),
          (2,3),(2,5),(2,6),(3,4),(3,6),(4,2),(4,5),(5,1),(5,3),(6,4)})),
 'dynamic_closed':Instance(((3,0),(5,6),(1,3),(-1,4),(5,6),(2,1),(-1,-1)),
     0,frozenset({6}),frozenset({(0,5),(1,0),(1,2),(1,5),(2,0),(2,3),(2,5),
                                 (3,0),(4,2),(4,3),(5,0),(5,1)})),
 'modular_unknown':OLD_FIXTURES['modular_positive_unknown'],
 'marking_unknown':OLD_FIXTURES['marking_barrier'],
}


def words(alphabet,bound):
    for n in range(bound+1):yield from product(range(alphabet),repeat=n)


def reference_trim(A):
    # Fixed-point reachability rather than the production BFS implementation.
    forward={A.start}; backward={A.final}
    while True:
        nf=forward|{q for p in forward for q in A.delta[p] if q>=0}
        nb=backward|{p for p,row in enumerate(A.delta) if any(q in backward for q in row)}
        if nf==forward and nb==backward:break
        forward,backward=nf,nb
    live=sorted(forward&backward)
    if A.start not in live:return None
    ids={p:i for i,p in enumerate(live)}
    return Domain(tuple(tuple(ids.get(q,-1) for q in A.delta[p]) for p in live),
                  ids[A.start],ids[A.final],tuple(A.labels[p] for p in live))


def window_filter(A,flags,anchor,Y,cap=100000):
    """Separate exact filter: retain the last m-1 letters AND all their cuts.

    This deliberately does not use failure links, a longest-prefix state, or
    the production filter's transition formulas. It has an exponential bound.
    """
    m=len(Y);t=A.labels[anchor]
    start=((),(A.start,));states=[start];ids={start:0};rows=[];labels=[];final=-1
    for key in states:
        if key is None:
            final=len(rows);rows.append((-1,)*A.alphabet);labels.append(A.labels[A.final]);continue
        buf,path=key;p=path[-1];row=[];labels.append(A.labels[p])
        for a,q in enumerate(A.delta[p]):
            if q<0:row.append(-1);continue
            b=buf+(a,);c=path+(q,)
            hit=len(b)>=m and b[-m:]==Y
            if hit and (A.labels[c[-m-1]],t) in flags:row.append(-1);continue
            if q==A.final:
                if hit and c[-m-1]==anchor:nxt=None
                else:row.append(-1);continue
            elif m==1:nxt=((),(q,))
            else:nxt=(b[-(m-1):],c[-min(m,len(c)):])
            if nxt not in ids:
                if cap is not None and len(states)>=cap:raise Capped('reference window cap')
                ids[nxt]=len(states);states.append(nxt)
            row.append(ids[nxt])
        rows.append(tuple(row))
    if final<0:return None
    return reference_trim(Domain(tuple(rows),0,final,tuple(labels)))


def equivalent(A,B):
    """Complete symmetric-difference search, not a word-length test."""
    if A is None or B is None:return A is None and B is None
    assert A.alphabet==B.alphabet
    start=(A.start,B.start);seen={start};queue=[start]
    for p,q in queue:
        if (p==A.final)!=(q==B.final):return False
        if p>=0 and q>=0:assert A.labels[p]==B.labels[q], 'state-label projection mismatch'
        for a in range(A.alphabet):
            u=A.delta[p][a] if p>=0 else -1;v=B.delta[q][a] if q>=0 else -1
            pair=(u,v)
            if pair not in seen:seen.add(pair);queue.append(pair)
    return True


def reference_tails(A,T):
    """Complete DAG-tail enumeration; return None for productive cycles."""
    allowed={p for p in range(A.k) if A.labels[p] not in T}
    good={A.final}
    while True:
        nxt=good|{p for p in allowed if any(q in good for q in A.delta[p])}
        if nxt==good:break
        good=nxt
    result=[]
    def visit(anchor,p,path,word):
        if p==A.final:result.append((anchor,word));return
        if p in path:raise RuntimeError('productive cycle')
        for a,q in enumerate(A.delta[p]):
            if q in good:visit(anchor,q,path|{p},word+(a,))
    try:
        for p,label in enumerate(A.labels):
            if label in T:visit(p,p,set(),())
    except RuntimeError:return None
    return result


def verify_return(A,flags,target,cert):
    """Check the supplied closed set using independently built pair edges."""
    assert cert['status']=='CLOSED' and cert['target']==target and cert['domain']==A.digest()
    edges={}
    for p in range(A.k):
        for q in range(A.k):
            if p==A.final or A.labels[p]==A.labels[q]:continue
            edges[p,q]=set()
            for a in range(A.alphabet):
                u=A.delta[p][a];v=A.delta[q][a]
                if u>=0 and v>=0 and u!=A.final and A.labels[u]!=A.labels[v]:edges[p,q].add((u,v))
    live={(p,q) for p,q in edges if q==A.final}
    while True:
        nxt=live|{v for v,es in edges.items() if es&live}
        if nxt==live:break
        live=nxt
    assert {tuple(v) for v in cert['productive']}==live
    R={tuple(v) for v in cert['reachable']}
    roots={(p,q) for p,q in live if A.labels[q]==target and (A.labels[p],target) in flags}
    assert roots<=R<=live
    for p,q in R:
        assert edges[p,q]&live<=R
        assert A.labels[q]!=target or (A.labels[p],target) in flags
    return len(R)


def verify_no_node(A,flags,targets,proof,counts):
    assert proof['status']=='NO' and proof['domain']==A.digest()
    T=set(targets)&set(A.labels)
    assert proof['targets']==sorted(T)
    # No-target language must be empty, checked by a separate fixed point.
    free={A.start} if A.labels[A.start] not in T else set()
    while True:
        nxt=free|{q for p in free for q in A.delta[p] if q>=0 and A.labels[q] not in T}
        if nxt==free:break
        free=nxt
    assert A.final not in free
    expected=reference_tails(A,T)
    assert expected is not None, 'NO contains a productive tail cycle'
    branches=proof['branches']
    assert len(branches)==len(expected)
    assert {(b['anchor'],tuple(b['tail'])) for b in branches}==set(expected)
    counts['negative_nodes']+=1
    for branch in branches:
        anchor=branch['anchor'];Y=tuple(branch['tail']);t=A.labels[anchor]
        assert branch['status']=='NO' and branch['target']==t
        # Prove exact filter language independently before relying on recursion.
        B=fixed_tail_filter(A,flags,anchor,Y,UNCAPPED)
        R=window_filter(A,flags,anchor,Y)
        assert equivalent(B,R)
        counts['negative_filter_equivalences']+=1
        if B is None:
            assert branch['reason']=='empty fixed-tail filter'
        else:
            verify_return(B,flags,t,branch['return_certificate'])
            counts['negative_return_certificates']+=1
            assert t in T
            verify_no_node(B,flags,T-{t},branch['child'],counts)


def verify_no(I,proof,counts=None):
    if counts is None:counts=Counter()
    assert proof['status']=='NO'
    assert len(proof['slices'])==len(I.finals)
    assert {s['final'] for s in proof['slices']}==set(I.finals)
    for sl in proof['slices']:
        f=sl['final'];norm=normalize(I,f)
        assert sl['status']=='NO'
        if norm is None:
            assert sl['reason']=='empty boundary slice';counts['boundary_no_slices']+=1
        else:
            J,order=norm
            assert sl['normalization']==list(order)
            A=Domain(J.delta,J.start,next(iter(J.finals)),tuple(range(J.k)))
            verify_no_node(A,J.flags,{t for p,t in J.flags},sl['result'],counts)
    counts['negative_proofs']+=1
    return counts


def all_acyclic_words(I):
    result=[]
    def go(p,w,seen):
        if p in I.bad:return
        if p in I.finals:result.append(w);return
        assert p not in seen
        for a,q in enumerate(I.delta[p]):
            if q>=0:go(q,w+(a,),seen|{p})
    go(I.start,(),set());return result


def self_test():
    rng=random.Random(SEED);counts=Counter();verdicts=Counter();fixtures={};full_cases=[]
    limits=Limits(3000,100000,3000,500)
    for name,I in FIXTURES.items():
        out=solve(I,UNCAPPED);prior=solve_with_tail_test(I)
        cs=original_closed_columns(I,UNCAPPED)
        fixtures[name]=dict(input=I.as_json(),status=out['status'],word=out.get('word'),
                            stats=out['stats'],prior_status=prior['status'],
                            initially_all_closed=all(c['all_closed'] for c in cs))
        full_cases.append(dict(name=name,input=I.as_json(),result=out,closure=cs))
        if out['status']=='YES':assert witness(I,tuple(out['word'])) and reverse_witness(I,tuple(out['word']))
        if out['status']=='NO':verify_no(I,out,counts)
    positive=FIXTURES['legal_repeats'];r=fixtures['legal_repeats']
    assert r['prior_status']=='UNKNOWN' and r['status']=='YES' and r['initially_all_closed']
    assert r['stats']['eliminations']==3 and r['word']==(0,1,0,0)
    assert witness(positive,(0,0))  # The solver does not promise shortest words.
    T={t for p,t in positive.flags}
    fullcols=Instance(positive.delta,0,positive.finals,
        frozenset((p,t) for t in T for p in range(positive.k) if p!=t and p not in positive.finals))
    assert solve_columns(fullcols)['status']=='NO'
    assert fixtures['recursive_no']['status']=='NO' and fixtures['recursive_no']['prior_status']=='UNKNOWN'
    assert fixtures['recursive_no']['stats']['eliminations']>=2
    assert fixtures['dynamic_closed']['status']=='YES' and not fixtures['dynamic_closed']['initially_all_closed']
    assert fixtures['modular_unknown']['status']==fixtures['marking_unknown']['status']=='UNKNOWN'
    counts['named_fixtures']=len(fixtures)

    # A concrete bad accepted word that passes every last-column check.
    M=FIXTURES['modular_unknown'];A=Domain(M.delta,M.start,next(iter(M.finals)),tuple(range(M.k)))
    bad=(1,)*4+(0,)+(1,)*6+(0,)
    assert M.accepted(bad) and not witness(M,bad) and not reverse_witness(M,bad)
    assert last_columns_spec(A,M.flags,{t for p,t in M.flags},bad)
    trace=M.run(bad)
    hits=[(i,j) for i in range(len(bad)+1) for j in range(i,len(bad)+1)
          if (trace[i],trace[j]) in M.flags and bad[i:i+len(bad)-j]==bad[j:]]
    assert hits==[(0,7)]
    counts['unsafe_last_only_regressions']=1

    # Original labels must remain grouped through state refinement. Treating
    # monitor copies as different targets can falsely certify a whole column.
    cover=Domain(((2,1),(2,0),(4,3),(4,2),(-1,-1)),0,4,(0,1,2,2,3))
    column=frozenset({(0,2)})
    assert return_certificate(cover,column,2,UNCAPPED)['status']=='UNKNOWN'
    wrong=Domain(cover.delta,0,4,tuple(range(5)))
    split_flags=frozenset({(0,2),(0,3)})
    assert all(return_certificate(wrong,split_flags,t,UNCAPPED)['status']=='CLOSED' for t in (2,3))
    cw=(1,0,1,1,0)
    assert last_columns_spec(cover,column,{2},cw) and not domain_witness(cover,column,{2},cw)
    counts['original_label_grouping_regressions']=1

    # An earlier occurrence overlapping the terminal one must be checked.
    overlap=Domain(((1,-1),(-1,2),(3,-1),(-1,4),(5,-1),(-1,-1)),0,5,tuple(range(6)))
    ow=(0,1,0,1,0); tail=(0,1,0)
    for flag,expected in [((0,2),False),((1,2),True)]:
        B=fixed_tail_filter(overlap,frozenset({flag}),2,tail,UNCAPPED)
        R=window_filter(overlap,frozenset({flag}),2,tail)
        assert equivalent(B,R)
        assert (B is not None and B.accepts(ow))==expected
        counts['explicit_overlapping_pattern_cases']+=1

    # All 1,024 raw three-state tables/proper-flag subsets. NO is certified,
    # not inferred from the short word scan.
    for flat in product(range(-1,3),repeat=4):
        delta=(flat[:2],flat[2:],(-1,-1))
        for mask in range(4):
            G=frozenset(p for j,p in enumerate(((0,1),(1,0))) if mask>>j&1)
            I=Instance(delta,0,frozenset({2}),G)
            out=solve(I,UNCAPPED);verdicts['three_state_'+out['status']]+=1
            assert out['status']!='UNKNOWN'
            old=solve_with_tail_test(I);assert old['status']==out['status']
            counts['complete_three_state_instances']+=1
            if out['status']=='NO':verify_no(I,out,counts)
            for w in words(2,5):
                actual=witness(I,w)
                assert actual==reverse_witness(I,w)
                if actual:assert out['status']=='YES'
                counts['three_state_word_comparisons']+=1

    # Complete finite languages, including diagonal/empty-suffix constraints.
    for _ in range(120):
        k=rng.randrange(2,9)
        delta=tuple(tuple(rng.choice([-1]+list(range(p+1,k))) for _ in (0,1))
                    for p in range(k-1))+((-1,-1),)
        finals=frozenset(p for p,row in enumerate(delta) if row==(-1,-1) and (p==k-1 or rng.random()<.3))
        G=frozenset((p,t) for p in range(k) for t in range(k) if rng.random()<.16)
        badstates=frozenset(p for p in range(k) if rng.random()<.06)
        I=Instance(delta,0,finals,G,badstates);ww=all_acyclic_words(I)
        expected=any(reverse_witness(I,w) for w in ww);out=solve(I,UNCAPPED)
        assert out['status']==('YES' if expected else 'NO')
        if out['status']=='NO':verify_no(I,out,counts)
        counts['complete_acyclic_instances']+=1;counts['complete_acyclic_words']+=len(ww)

    # Random productive domains: closure implication and regular-filter equivalence.
    filter_samples=0
    for _ in range(400):
        k=rng.randrange(3,8)
        delta=tuple(tuple(rng.randrange(-1,k) for _ in (0,1)) for p in range(k-1))+((-1,-1),)
        G=frozenset((p,t) for p in range(k-1) for t in range(k-1) if p!=t and rng.random()<.23)
        I=Instance(delta,0,frozenset({k-1}),G)
        norm=normalize(I,k-1)
        if norm is None:continue
        counts['random_productive_instances']+=1
        J,_=norm;A=Domain(J.delta,J.start,next(iter(J.finals)),tuple(range(J.k)));T={t for p,t in J.flags}
        closed=True
        for t in sorted(T):
            cert=return_certificate(A,J.flags,t,UNCAPPED)
            if cert['status']=='CLOSED':verify_return(A,J.flags,t,cert);counts['return_closed_certificates']+=1
            else:closed=False
        for w in words(2,8):
            if closed:assert domain_witness(A,J.flags,T,w)==last_columns_spec(A,J.flags,T,w)
            counts['last_column_word_comparisons']+=int(closed)
        out=solve(J,limits);verdicts['random_'+out['status']]+=1
        if closed:
            counts['random_initially_closed_instances']+=1
            assert out['status']!='UNKNOWN', 'Unexpected cap in small closed corpus'
        if out['status']=='YES':assert witness(J,tuple(out['word'])) and reverse_witness(J,tuple(out['word']))
        if out['status']=='NO':verify_no(J,out,counts)
        if filter_samples>=120:continue
        for anchor in range(A.k):
            if anchor==A.final:continue
            for Y in words(2,4):
                path=A.run(Y,anchor)
                if not Y or path is None or path[-1]!=A.final:continue
                fast=fixed_tail_filter(A,J.flags,anchor,Y,UNCAPPED)
                ref=window_filter(A,J.flags,anchor,Y)
                assert equivalent(fast,ref)
                counts['complete_filter_equivalences']+=1;filter_samples+=1
                for w in words(2,7):
                    yes=fast is not None and fast.accepts(w)
                    assert yes==filtered_spec(A,J.flags,anchor,Y,w)
                    counts['fixed_tail_literal_comparisons']+=1
                if filter_samples>=120:break
            if filter_samples>=120:break

    # Reject omissions in a genuinely recursive NO proof.
    original=solve(FIXTURES['recursive_no'],UNCAPPED)
    damaged=copy.deepcopy(original)
    damaged['slices'][0]['result']['branches'].pop()
    try:verify_no(FIXTURES['recursive_no'],damaged)
    except AssertionError:counts['corrupt_proofs_rejected']+=1
    else:raise AssertionError('Incomplete tail coverage accepted')
    damaged=copy.deepcopy(original)
    def break_certificate(node):
        for b in node.get('branches',[]):
            c=b.get('return_certificate')
            if c is not None:
                c['productive']=[];return True
            if break_certificate(b.get('child',{})):return True
        return False
    assert break_certificate(damaged['slices'][0]['result'])
    try:verify_no(FIXTURES['recursive_no'],damaged)
    except AssertionError:counts['corrupt_proofs_rejected']+=1
    else:raise AssertionError('Corrupted return certificate accepted')
    capped=solve(FIXTURES['legal_repeats'],Limits(1,1,1,1))
    assert capped['status']=='UNKNOWN';counts['explicit_cap_cases']+=1
    try:Limits(states=0)
    except ValueError:counts['malformed_inputs_rejected']+=1
    else:raise AssertionError('Invalid cap accepted')

    return dict(status='PASS',base_commit=BASE,seed=SEED,counts=dict(sorted(counts.items())),
                verdicts=dict(sorted(verdicts.items())),fixtures=fixtures,
                last_only_counterexample=dict(word=bad,violation_cuts=hits,
                    original_states=[trace[i] for i in hits[0]],last_columns_pass=True),
                full_cases=full_cases,
                evidence_limits=['Written proof, not independent mathematical review or Lean.',
                  'Complete on the return-closed class. Arbitrary failed branches remain UNKNOWN.',
                  'Finite scans are regression evidence; NO uses complete certificate trees.',
                  'The old C077 period lemma is a dependency, not newly independently certified.'])


def compact(out):return {k:v for k,v in out.items() if k!='full_cases'}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path);p.add_argument('--full-output',type=Path)
    p.add_argument('--verify-instance',type=Path)
    p.add_argument('--verify-certificate',type=Path)
    args=p.parse_args()
    if not __debug__:p.error('Run with assertions enabled, not python -O')
    if bool(args.verify_instance) != bool(args.verify_certificate):
        p.error('Certificate replay requires both --verify-instance and --verify-certificate')
    if args.verify_instance:
        I=from_json(json.loads(args.verify_instance.read_text()))
        certificate=json.loads(args.verify_certificate.read_text())
        counts=Counter();verify_no(I,certificate,counts)
        print(json.dumps(dict(status='VERIFIED_NO',counts=dict(counts)),indent=2,sort_keys=True))
        return
    out=self_test();small=compact(out)
    text=json.dumps(small,indent=2,sort_keys=True)+'\n'
    if args.output:args.output.write_text(text)
    if args.full_output:args.full_output.write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(text)

if __name__=='__main__':main()
