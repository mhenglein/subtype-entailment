"""Reproducible checks for the realizable last-flag length spectrum.

The finite checks are not all-length proofs. The theorem is in the linked note.
The direct oracle uses reversed borders, not the new action/template machinery.
"""
import hashlib
import json
import random
from collections import Counter, deque
from dataclasses import replace
from itertools import product
from pathlib import Path

from border_lab import Instance, Sandwich, border_witness, necessary, witness, words
from lastflag_spectrum import (ActionMonoid, boundary_slice, decide, is_lastflag,
                               length_schema, realize_template, spectrum,
                               spectrum_prefix, _reach)

SEED = 2026090719


def reversed_lengths(I, w):
    c = I.run(w)
    if not I.admissible(w):
        return set()
    n, rho = len(w), w[::-1]
    if any((p,p) in I.flags or (p,c[-1]) in I.flags for p in c):
        return set()
    result = set()
    for i in range(n):
        for j in range(i+1,n):
            length = n-j
            if ((c[i],c[j]) in I.flags and rho[:length] == rho[j-i:n-i]
                and not any((c[i+t],c[j+t]) in I.flags for t in range(1,length+1))):
                result.add(length)
    return result


def complete_acyclic_words(I):
    """The caller's graph has only increasing edges; no length cutoff is used."""
    result, pending = [], [(I.start,'')]
    while pending:
        q,w = pending.pop()
        if q in I.final:
            result.append(w)
        for a,r in zip(I.alphabet,I.delta[q]):
            if r>=0:
                assert r>q
                pending.append((r,w+a))
    return result


def check_certificates(I, s, counts):
    for item in s['slices']:
        if item.get('empty_slice') or item['status']=='UNKNOWN':
            continue
        J,_ = boundary_slice(I,item['final'])
        if item['status']=='FINITE':
            if item['H']:
                sample=realize_template(item['maximum_certificate'])
                assert is_lastflag(J,**sample) and is_lastflag(I,**sample)
                assert len(sample['word'])-sample['j']==item['H']
                assert item['H'] in reversed_lengths(I,sample['word'])
                counts['attained_maximum_certificates']+=1
            else:
                assert item['maximum_certificate'] is None
        else:
            previous=-1
            for m in (1,2,4,10,40):
                sample=realize_template(item['pumping_certificate'],m)
                assert is_lastflag(J,**sample) and is_lastflag(I,**sample)
                length=len(sample['word'])-sample['j']
                assert length>previous and length in reversed_lengths(I,sample['word'])
                assert not witness(I,sample['word']) and not border_witness(I,sample['word'])
                previous=length
                counts['pumping_instances']+=1

def old_bound(J):
    k=len(J.delta);f=next(iter(J.final));reach=[_reach(J.delta,[p]) for p in range(k)]
    vertices=[(p,q) for p in range(k) for q in range(k) if p!=q and p!=f]
    edges={pq:[] for pq in vertices}
    for p,q in vertices:
        for a in range(len(J.alphabet)):
            t=(J.delta[p][a],J.delta[q][a])
            if t in edges and t not in J.flags:
                edges[p,q].append(t)
    roots={(p,q) for p,q in J.flags if p!=q and p!=f and q!=f and q in reach[p]}
    seen=set(roots);todo=list(roots)
    while todo:
        for q in edges[todo.pop()]:
            if q not in seen: seen.add(q);todo.append(q)
    back={p:[] for p in vertices}
    for p,row in edges.items():
        for q in row:back[q].append(p)
    live={(p,f) for p in range(k) if p!=f};todo=list(live)
    while todo:
        for q in back[todo.pop()]:
            if q not in live:live.add(q);todo.append(q)
    live &=seen
    indeg={p:0 for p in live}
    for p in live:
        for q in edges[p]:
            if q in live:indeg[q]+=1
    todo=deque(p for p in live if indeg[p]==0);dist={p:0 for p in roots & live};done=0
    while todo:
        p=todo.popleft();done+=1
        for q in edges[p]:
            if q in live:
                if p in dist:dist[q]=max(dist.get(q,-1),dist[p]+1)
                indeg[q]-=1
                if not indeg[q]:todo.append(q)
    if done<len(live):return None
    return max((dist.get((p,f),0) for p in range(k)),default=0)


def check():
    rng=random.Random(SEED)
    counts=Counter()
    statuses=Counter()
    for k in range(1,4):
        pairs=[(p,q) for p in range(k-1) for q in range(k-1) if p!=q]
        for flat in product(range(-1,k),repeat=2*(k-1)):
            delta=tuple(tuple(flat[2*p:2*p+2]) for p in range(k-1))+((-1,-1),)
            for mask in range(1<<len(pairs)):
                I=Instance(delta,frozenset({k-1}),frozenset(p for j,p in enumerate(pairs) if mask>>j&1))
                s=spectrum(I,None,None)
                assert s['status']=='FINITE'
                counts['exhaustive_small_instances']+=1
                check_certificates(I,s,counts)
                answer=decide(I,None,None,None)
                statuses['small_'+answer['status']]+=1
                for w in words('01',7):
                    good=witness(I,w)
                    assert good==border_witness(I,w)==necessary(I,w,s['H'],0)
                    assert all(l<=s['H'] for l in reversed_lengths(I,w))
                    if answer['status']=='NO': assert not good
                    counts['small_word_checks']+=1

    for case in range(240):
        k=rng.randrange(1,9)
        delta=[]
        for p in range(k):
            delta.append(tuple(rng.choice([-1]+list(range(p+1,k))) for _ in range(2)))
        finals=frozenset(p for p,row in enumerate(delta) if row==(-1,-1) and rng.random()<.8)
        I=Instance(tuple(delta),finals,
                   frozenset((p,q) for p in range(k) for q in range(k) if rng.random()<.12),
                   frozenset(p for p in range(k) if rng.random()<.08))
        all_words=complete_acyclic_words(I)
        exact=set().union(*(reversed_lengths(I,w) for w in all_words))
        s=spectrum(I,None,None)
        assert s['status']=='FINITE' and s['H']==max(exact,default=0)
        schema=length_schema(I,None,None)
        assert spectrum_prefix(schema,k)==sorted(exact)
        good=[w for w in all_words if witness(I,w)]
        answer=decide(I,None,None,None)
        assert answer['status']==('YES' if good else 'NO')
        check_certificates(I,s,counts)
        counts['complete_acyclic_oracles']+=1
        counts['complete_acyclic_accepted_words']+=len(all_words)
        statuses['acyclic_'+answer['status']]+=1

    for case in range(600):
        k=rng.randrange(3,8)
        delta=tuple(tuple(rng.randrange(-1,k) for _ in range(2)) for _ in range(k-1))+((-1,-1),)
        finals=frozenset(p for p,row in enumerate(delta) if row==(-1,-1) and (p==k-1 or rng.random()<.5))
        I=Instance(delta,finals,
                   frozenset((p,q) for p in range(k) for q in range(k) if rng.random()<(.05 if case%3 else .15)),
                   frozenset(p for p in range(k) if rng.random()<.03))
        s=spectrum(I,5000,2000000)
        counts['random_instances']+=1
        statuses['random_'+s['status']]+=1
        check_certificates(I,s,counts)
        for item in s['slices']:
            if item.get('empty_slice') or item['status']=='UNKNOWN':continue
            J,_=boundary_slice(I,item['final']);old=old_bound(J)
            if old is not None:
                assert item['status']=='FINITE' and item['H']<=old
                counts['old_certificate_subsumptions']+=1
        for w in words('01',7):
            good=witness(I,w)
            assert good==border_witness(I,w)
            lengths=reversed_lengths(I,w)
            if s['status']=='FINITE':
                assert all(l<=s['H'] for l in lengths)
                assert good==necessary(I,w,s['H'],0)
            counts['random_word_checks']+=1

    # Independent action-class cycle oracle: ancestor subgraphs and DFS,
    # not the production Kahn computation. Includes nonempty identity words.
    for n in range(1,4):
        for raw in product(range(n),repeat=2*n):
            generators=[tuple(raw[:n]),tuple(raw[n:])]
            monoid=ActionMonoid.build(generators,'01',None)
            for target in range(len(monoid.actions)):
                ancestors={target};pending=[target]
                while pending:
                    for p,_ in monoid.incoming[pending.pop()]:
                        if p not in ancestors:ancestors.add(p);pending.append(p)
                color={};memo={}
                def visit(q):
                    if color.get(q)==1:raise RuntimeError('cycle')
                    if color.get(q)==2:return memo[q]
                    color[q]=1
                    value=0 if q==target else -1000000
                    for t in monoid.edges[q]:
                        if t in ancestors:value=max(value,1+visit(t))
                    color[q]=2;memo[q]=value
                    return value
                try: maximum=visit(0)
                except RuntimeError:maximum=None
                assert monoid.maximum[target]==maximum
                if maximum is None:
                    lasso=monoid.lasso(target)
                    for m in (0,1,3):
                        w=lasso['prefix']+lasso['loop']*m+lasso['suffix']
                        assert monoid.action_index(w)==target
                        counts['action_lasso_checks']+=1
                else:
                    assert len(monoid.longest[target])==maximum
                    assert monoid.action_index(monoid.longest[target])==target
                counts['action_class_checks']+=1
            counts['action_generator_pairs']+=1

    fixtures={
      'strict_five_state':Instance(((2,1),(3,4),(3,2),(4,3),(-1,-1)),frozenset({4}),frozenset({(0,1)})),
      'nonflat_positive':Instance(((1,-1),(2,3),(2,1),(4,-1),(-1,5),(-1,-1)),frozenset({5}),frozenset({(0,3),(1,3)})),
      'nonflat_negative':Instance(((1,-1),(2,3),(2,1),(4,-1),(-1,5),(-1,-1)),frozenset({5}),frozenset({(0,3),(1,3),(2,3)})),
      'nonregular_positive':Instance(((0,1),(2,-1),(2,3),(-1,-1)),frozenset({3}),frozenset({(0,1)})),
      'necessary_incomplete':Instance(((2,1),(2,1),(-1,3),(4,3),(-1,-1)),frozenset({4}),frozenset({(0,2),(0,3),(1,2)})),
      'unbounded_with_short_detection':Instance(((-1,1),(2,1),(3,-1),(-1,4),(5,4),(6,-1),(-1,-1)),frozenset({6}),frozenset({(0,3),(4,5)})),
    }
    expected={'strict_five_state':'YES','nonflat_positive':'YES','nonflat_negative':'NO',
              'nonregular_positive':'UNKNOWN','necessary_incomplete':'UNKNOWN',
              'unbounded_with_short_detection':'UNKNOWN'}
    outputs={}
    for name,I in fixtures.items():
        answer=decide(I,None,None,None)
        assert answer['status']==expected[name]
        outputs[name]={'delta':I.delta,'flags':sorted(I.flags),'final':sorted(I.final),**answer}
        check_certificates(I,answer['analysis'],counts)
        schema=length_schema(I,None,None)
        outputs[name]['spectrum_through_12']=spectrum_prefix(schema,12)
        for w in words('01',11):
            assert witness(I,w)==border_witness(I,w)
            lengths=reversed_lengths(I,w)
            assert lengths<=set(outputs[name]['spectrum_through_12'])
            if name=='strict_five_state' and I.admissible(w):
                assert witness(I,w)==(w!='11')
            if name=='unbounded_with_short_detection':
                assert not witness(I,w) and not necessary(I,w,1,0)
            counts['fixture_word_checks']+=1
    strict=fixtures['strict_five_state']
    assert old_bound(strict) is None
    assert outputs['strict_five_state']['analysis']['H']==1
    assert outputs['strict_five_state']['spectrum_through_12']==[1]
    assert outputs['nonregular_positive']['spectrum_through_12']==list(range(2,13))
    assert outputs['necessary_incomplete']['spectrum_through_12']==list(range(1,13))
    assert outputs['unbounded_with_short_detection']['spectrum_through_12']==[1]+list(range(3,13))
    assert Sandwich(fixtures['unbounded_with_short_detection'],1,0).search()['status']=='NO'
    for n in range(1,41):
        I=fixtures['unbounded_with_short_detection'];w=('1'*n+'00')*2
        assert is_lastflag(I,w,0,n+2) and {1,n+2}<=reversed_lengths(I,w)
        counts['unbounded_but_short_detectable_family']+=1

    # All caps remain UNKNOWN; malformed parameters are rejected; nonterminal
    # inputs are unsupported, not silently terminalized. Empty and multi-final
    # behavior is already covered by the complete acyclic-language oracles.
    assert spectrum(strict,max_monoid=1)['status']=='UNKNOWN'
    assert spectrum(strict,max_checks=1)['status']=='UNKNOWN'
    assert decide(strict,max_search_states=1)['status']=='UNKNOWN'
    assert length_schema(strict,max_monoid=1)['status']=='UNKNOWN'
    assert spectrum(Instance(((0,0),),frozenset({0})))['status']=='UNSUPPORTED'
    for kwargs in ({'max_monoid':0},{'max_checks':-1},{'max_monoid':True}):
        try:spectrum(strict,**kwargs)
        except ValueError:pass
        else:raise AssertionError(kwargs)
    try:spectrum_prefix({'status':'UNKNOWN'},10)
    except ValueError:pass
    else:raise AssertionError('incomplete schema accepted')
    counts['scope_and_cap_regressions']=9
    return {'base_main':'8e6c2e6c13754436871ff440cd52cd3e60294a74','seed':SEED,
            'status':'PASS','proof_status':'WRITTEN; independent review pending; not Lean-checked',
            'counts':dict(sorted(counts.items())),'statuses':dict(sorted(statuses.items())),
            'fixtures':outputs,'failures':0,
            'limits':{'random_monoid_cap':5000,'random_combination_cap':2000000,
                      'small_and_random_word_cutoff':7,'fixture_word_cutoff':11,
                      'full_repository_ci':False,'lean_build':False}}


if __name__=='__main__':
    result=check()
    destination=Path(__file__).resolve().parents[1]/'results'/'lastflag-spectrum.json'
    destination.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
