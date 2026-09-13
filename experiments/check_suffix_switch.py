#!/usr/bin/env python3
"""Deterministic independent oracles for the supplied suffix-switch class.

No claim of new coverage beyond the earlier target-frontier methods. Finite
oracles are complete for their supplied finite languages or fixed master words.
"""
from collections import Counter, deque
from itertools import product
from pathlib import Path
import argparse, json, random
from suffix_switch import (DFA, Description, Edge, universal, finite_language,
    compile_tokens, compile_binary, encode, suffixes, materialize,
    semantic_witness, witness_direct, witness_reverse, solve, two_reference_example)
from scheme_cost_barrier import minimum_scheme_cost, source_cuts


def fixed_master_oracle(D, data):
    """Full finite graph on control/output states, using literal fixed words."""
    tails=suffixes(D,data)
    if not D.master_guard.accepts(tails[0]): return False
    todo=deque([(D.start,D.output_guard.start)]); seen=set(todo)
    while todo:
        r,q=todo.popleft()
        final=D.output_guard.run((D.switch,)+tails[0]+(D.end,),q)
        if r in D.finals and final is not None and final[-1] in D.output_guard.finals: return True
        for e in D.edges:
            if e.source!=r or not e.guard.accepts(tails[e.kind]): continue
            c=D.output_guard.run(tails[e.kind]+(D.end,),q)
            if c is not None and (e.target,c[-1]) not in seen:
                node=e.target,c[-1]; seen.add(node); todo.append(node)
    return False


def finite_accepted_words(M):
    """Exhaust a proved acyclic DFA, without a guessed word-length cutoff."""
    colour={}
    def acyclic(q):
        if colour.get(q)==1: raise AssertionError('Finite oracle unexpectedly cyclic')
        if colour.get(q)==2: return
        colour[q]=1
        for p in M.delta[q]:
            if p>=0: acyclic(p)
        colour[q]=2
    acyclic(M.start)
    todo=[(M.start,())]
    while todo:
        q,w=todo.pop()
        if q in M.finals: yield w
        for a,p in enumerate(M.delta[q]):
            if p>=0: todo.append((p,w+(a,)))


def literal_cost_oracle(I,w):
    """All phase partitions of a fixed short word, no Z algorithm or DP table."""
    c,cuts=source_cuts(I,w)
    def rec(i):
        if i==len(cuts): return 0
        best=1+rec(i+1); a=cuts[i]
        for j in range(i+1,len(cuts)):
            b=cuts[j]
            if c[a]!=c[b]: continue
            for end in range(j,len(cuts)):
                e=cuts[end]; length=b-a
                if (e-a)%length: continue
                m=(e-a)//length
                if w[a:e]==w[a:b]*m:
                    best=min(best,1+j-i+rec(end+1))
        return best
    return rec(0)


def main_checks():
    rng=random.Random(2026091362); C=Counter(); verdicts=Counter()
    tiny=((),(0,),(1,))
    # Five independent forms: grammar, token cuts/borders, binary cuts/borders.
    for h in (1,2):
        A=h+4; U=universal(A)
        D=Description(h,1,0,frozenset({0}),tuple(Edge(0,j,0,U) for j in range(h)),U,U)
        I=compile_tokens(D); B,code=compile_binary(I)
        datas=list(product(tiny,repeat=h))
        for master in datas:
            tail=suffixes(D,master)[0]
            unit_choices=[suffixes(D,x)[j]+(D.end,) for j in range(h)
                          for x in product(tiny,repeat=h)]
            # Deduplicate logically identical later suffixes.
            unit_choices=sorted(set(unit_choices))
            for m in range(3):
                for units in product(unit_choices,repeat=m):
                    w=sum(units,())+(D.switch,)+tail+(D.end,)
                    expected=semantic_witness(D,w); bits=encode(w,code)
                    assert expected==witness_direct(I,w)==witness_reverse(I,w)
                    assert expected==witness_direct(B,bits)==witness_reverse(B,bits)
                    C['structured_five_way_comparisons']+=1
    # Complete finite candidate oracles with independently selectable blocks.
    for trial in range(16):
        h=1+trial%2; A=h+4; U=universal(A)
        shell=Description(h,1,0,frozenset({0}),(),U,U)
        all_data=list(product(tiny,repeat=h))
        master_words=[suffixes(shell,x)[0] for x in all_data if rng.random()<.6]
        master=finite_language(master_words,A)
        edges=[]
        for r in range(2):
            for j in range(h):
                words=sorted({suffixes(shell,x)[j] for x in all_data if rng.random()<.5})
                edges.append(Edge(r,j,r+1,finite_language(words,A)))
        D=Description(h,3,0,frozenset({2}),tuple(edges),master,U)
        I=compile_tokens(D); expected=False
        for w in finite_accepted_words(I.machine):
            a=witness_direct(I,w)
            assert a==witness_reverse(I,w)==semantic_witness(D,w)
            expected|=a; C['complete_finite_candidate_words']+=1
        result=solve(D); assert result['status']==('YES' if expected else 'NO')
        assert result['status']!='NO' or result['exhausted']
        verdicts[result['status']]+=1; C['complete_finite_instances']+=1
    # Recurrence unbounded, but fixed master permits an independent exact graph.
    for trial in range(60):
        h=1+trial%2; A=h+4; U=universal(A)
        data=tuple(rng.choice(tiny) for _ in range(h))
        temp=Description(h,1,0,frozenset({0}),(),U,U)
        master=finite_language((suffixes(temp,data)[0],),A)
        def random_guard():
            return DFA(tuple(tuple(rng.randrange(-1,2) for _ in range(A)) for _ in range(2)),
                       0,frozenset(q for q in range(2) if rng.random()<.6))
        guard=random_guard(); output=random_guard()
        edges=tuple(Edge(r,j,rng.randrange(3),guard) for r in range(3) for j in range(h))
        D=Description(h,3,0,frozenset(r for r in range(3) if rng.random()<.6),edges,master,output)
        expected=fixed_master_oracle(D,data); result=solve(D)
        assert result['status']==('YES' if expected else 'NO')
        if expected:
            I=compile_tokens(D); assert witness_direct(I,tuple(result['word']))
        verdicts[result['status']]+=1; C['complete_fixed_master_graphs']+=1
    demo=two_reference_example(); result=solve(demo)
    assert result['status']=='YES' and result['sequence']==[0,1]
    T=suffixes(demo,result['data'])
    assert T[0]+T[1]!=T[1]+T[0]
    assert solve(demo,max_actions=1)['status']=='UNKNOWN'
    assert solve(demo,max_tuples=1)['status']=='UNKNOWN'
    C['cap_regressions']=2
    # Empty data and no units are allowed; disjoint shared assignments are not.
    A=5; U=universal(A)
    empty=Description(1,1,0,frozenset({0}),(),U,U)
    assert solve(empty)['status']=='YES'
    bad=Description(1,2,0,frozenset({1}),(Edge(0,0,1,finite_language(((2,1),),A)),),
                    finite_language(((2,0),),A),U)
    assert solve(bad)['status']=='NO'; C['shared_assignment_regressions']=2
    # Exhaust raw binary strings for a small generated instance.
    I,code=compile_binary(compile_tokens(empty))
    for length in range(13):
        for w in product((0,1),repeat=length):
            assert witness_direct(I,w)==witness_reverse(I,w)
            C['raw_binary_comparisons']+=1
    # Independent cost partitions on short paths, including powers that help.
    from suffix_switch import Instance
    for trial in range(100):
        n=rng.randrange(2,6)
        delta=tuple(tuple(rng.randrange(-1,n) for _ in range(2)) for _ in range(n-1))+((-1,-1),)
        G=frozenset((q,n-1) for q in range(n) if rng.random()<.7)
        I=Instance(DFA(delta,0,frozenset({n-1})),G)
        for length in range(7):
            for w in product((0,1),repeat=length):
                if I.machine.accepts(w):
                    assert minimum_scheme_cost(I,w)['cost']==literal_cost_oracle(I,w)
                    C['exact_cost_partition_oracles']+=1
    return dict(status='PASS',seed=2026091362,counts=dict(sorted(C.items())),
                complete_oracle_verdicts=dict(sorted(verdicts.items())),
                demo=dict(data=result['data'],sequence=result['sequence'],word=result['word']),
                scope='Supplied suffix dictionary; targets confined to final master. Not general coverage.',
                evidence='Executed finite checks, no Lean or independent mathematical review')


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__); p.add_argument('--output',type=Path); args=p.parse_args()
    if not __debug__: p.error('Assertions must be enabled')
    out=main_checks(); text=json.dumps(out,indent=2,sort_keys=True)+'\n'
    if args.output: args.output.write_text(text)
    print(text)
