"""E033: all-cuts, finite-language oracles, and nonconvergent budget tests."""
import itertools
import json
import random
from pathlib import Path
from math import prod
from dataclasses import replace

from border_lab import Instance, words, witness, border_witness, necessary, Sandwich
from word_sync import BinaryDFA, encode_blocks, compile_sync, solve_sync
from delimited_blocks import BlockSystem, block_witness, solve_blocks
from terminal_realization import realize
from denial_bridge import Canonical

ROOT = Path(__file__).resolve().parents[1]


def incomplete_necessary_checks():
    starts0 = BinaryDFA(((1, -1), (1, 1)), frozenset({1}))
    starts1 = BinaryDFA(((-1, 1), (1, 1)), frozenset({1}))
    # Explicit five-state flat NO instance, independently proved by n<m, n=m, n>m.
    I = Instance(((2,1),(2,1),(-1,3),(4,3),(-1,-1)),
                 frozenset({4}),frozenset({(0,2),(0,3),(1,2)}))
    no = solve_sync((starts0, starts1), max_states=None)
    assert no['status'] == 'NO'
    counts = dict(position_pairs=0, budget_predicates=0, finite_necessary_graphs=0, exponent_vectors=0)
    for n in range(10):
        for m in range(1,11):
            word='1'*n+'0'+'1'*m+'0'
            assert I.admissible(word) and not witness(I,word) and not border_witness(I,word)
            counts['exponent_vectors'] += 1
    rows = []
    for n in range(16):
        w = '1'*n+'0'+'1'*(n+1)+'0'
        c = I.run(w)
        viol = [(i, j) for i in range(len(w)+1) for j in range(i, len(w)+1)
                if (c[i], c[j]) in I.flags and w[i:].startswith(w[j:])]
        assert viol == [(0, n+2)], (n, viol)
        counts['position_pairs'] += 1
        assert not witness(I, w) and not border_witness(I, w)
        for L in range(15):
            for D in range(15):
                expected = n+1 > L and n+2 > D
                assert necessary(I, w, L, D) == expected
                counts['budget_predicates'] += 1
        if n in (0, 1, 3, 10, 15):
            rows.append(dict(n=n, length=len(w), source=0, target=n+2,
                             violating_suffix=n+1, violating_gap=n+2))
    for L in range(5):
        for D in range(5):
            ans = Sandwich(I, L, D).search(200000)
            assert ans['status'] == 'YES', (L, D, ans)
            assert necessary(I, ans['word'], L, D) and not witness(I, ans['word'])
            counts['finite_necessary_graphs'] += 1
    R = realize(I)
    canon_checks = 0
    for n in range(4):
        w = '1'*n+'0'+'1'*(n+1)+'0'
        assert Canonical(R.variables, R.constraints, R.alpha, R.beta, w).errors()
        canon_checks += 1
    return dict(status='PASS', states=len(I.delta), flags=len(I.flags),
                independent_sync_NO_fixture=no, counts=counts, examples=rows,
                subtype_variables=R.variables, subtype_constraints=len(R.constraints),
                rejected_canonical_paths=canon_checks,
                all_length_statement='For every L,D some non-witness passes Necessary(L,D); witness language is empty')


def finite_language(m):
    # Caller supplies an acyclic table: every data edge increases its state.
    assert all(t < 0 or t > q for q, row in enumerate(m.delta) for t in row)
    return tuple(w for w in words('01', len(m.delta)-1) if m.accepts(w))


def main():
    rng = random.Random(2026090651)
    counts = dict(finite_instances=0, finite_tuples=0, formula_binary_comparisons=0,
                  cyclic_instances=0, cyclic_tuples=0, dictionary_instances=0, dictionary_tuples=0, canonical_models=0,
                  guards=0, caps=0, independent_sync_decisions=0)
    finite_verdicts = {'YES':0, 'NO':0, 'UNKNOWN':0}
    cyclic_verdicts = {'YES':0, 'NO':0, 'UNKNOWN':0}
    samples = []
    # Acyclic input DFAs provide a fully enumerated independent all-length oracle.
    for trial in range(350):
        r = rng.randrange(1, 5)
        ms = []
        for _ in range(r):
            n = rng.randrange(1, 5)
            table = tuple(tuple(rng.choice([-1]+list(range(q+1, n))) for _ in range(2)) for q in range(n))
            ms.append(BinaryDFA(table, frozenset(q for q in range(n) if rng.random() < .6), rng.randrange(n)))
        ms = tuple(ms)
        nodes = [(i, q) for i, m in enumerate(ms) for q in range(len(m.delta))]+[(r,0)]
        flags = frozenset((x,y) for x in nodes for y in nodes if rng.random() < .035)
        bad = frozenset(x for x in nodes if rng.random() < .025)
        sys = BlockSystem(ms, flags, bad)
        I, _ = sys.compile()
        good = []
        for blocks in itertools.product(*(finite_language(m) for m in ms)):
            w = encode_blocks(blocks)
            a = witness(I,w)
            assert a == border_witness(I,w) == block_witness(sys,blocks)
            counts['finite_tuples'] += 1
            counts['formula_binary_comparisons'] += 1
            if a:
                good.append(blocks)
        answer = solve_blocks(sys, max_states=None, max_transitions=None)
        counts['finite_instances'] += 1
        finite_verdicts[answer['status']] += 1
        assert (answer['status']=='YES') == bool(good), (sys,answer,good)
        assert answer['status'] != 'UNKNOWN'
    # Dense finite languages: complete independent oracle from the supplied dictionaries.
    def dictionary_dfa(dictionary):
        paths={'':0}; table=[[-1,-1]]; finals=set()
        for w in sorted(dictionary):
            prefix=''
            for a in w:
                nxt=prefix+a
                if nxt not in paths:
                    paths[nxt]=len(table);table.append([-1,-1])
                table[paths[prefix]][int(a)]=paths[nxt]
                prefix=nxt
            finals.add(paths[prefix])
        return BinaryDFA(tuple(map(tuple,table)),frozenset(finals))
    dictionary_verdicts={'YES':0,'NO':0,'UNKNOWN':0}
    vocabulary=tuple(words('01',2))
    for trial in range(120):
        r=rng.randrange(2,5)
        dictionaries=[tuple(sorted(rng.sample(vocabulary,rng.randrange(2,6)))) for _ in range(r)]
        ms=tuple(dictionary_dfa(d) for d in dictionaries)
        flags=frozenset(((i,p),(j,q)) for i in range(r) for j in range(i+1,r)
                        for p in range(len(ms[i].delta)) for q in range(len(ms[j].delta))
                        if rng.random()<.055)
        sys=BlockSystem(ms,flags)
        I,_=sys.compile()
        found=False
        for blocks in itertools.product(*dictionaries):
            good=witness(I,encode_blocks(blocks))
            assert good==border_witness(I,encode_blocks(blocks))==block_witness(sys,blocks)
            counts['dictionary_tuples']+=1
            counts['formula_binary_comparisons']+=1
            found |=good
        out=solve_blocks(sys,max_states=None,max_transitions=None)
        assert (out['status']=='YES')==found and out['status']!='UNKNOWN', (trial,sys,out)
        counts['dictionary_instances']+=1;dictionary_verdicts[out['status']]+=1
    U = BinaryDFA(((0,0),), frozenset({0}))
    # A hit involving a non-final stage is harmless when later blocks differ.
    fixture = BlockSystem((U,U,U), frozenset({((0,0),(1,0))}))
    good = ('','0','1')
    assert block_witness(fixture,good)
    assert not block_witness(fixture,('','0','0'))
    answer = solve_blocks(fixture, max_states=None, max_transitions=None)
    assert answer['status']=='YES' and answer['blocks'][1] != answer['blocks'][2]
    counts['guards'] += 2
    samples.append(dict(name='context_guard_needed',result=answer))
    # No valid match can begin twice in the same data stage and include its delimiter.
    single = BlockSystem((BinaryDFA(((1,-1),(2,-1),(-1,-1)),frozenset({2})),),
                         frozenset({((0,0),(0,1))}))
    single_answer = solve_blocks(single,max_states=None,max_transitions=None)
    assert single_answer['status']=='YES' and single_answer['blocks']==('00',)
    # The same flags on the un-delimited word 00 reject it: marker insertion is not a reduction.
    plain = Instance(((1,-1),(2,-1),(-1,-1)),frozenset({2}),frozenset({(0,1)}))
    assert not witness(plain,'00')
    counts['guards'] += 1
    samples.append(dict(name='delimiter_insertion_is_not_sound_for_general_inputs',plain_word='00',
                        encoded_word=single_answer['word']))
    cap = solve_blocks(fixture,max_states=1)
    assert cap['status']=='UNKNOWN'
    counts['caps'] += 1
    # Random genuinely cyclic stages, arbitrary annotations, exhaustive short tuples.
    for trial in range(180):
        r = rng.randrange(2,5)
        ms = []
        for _ in range(r):
            n = rng.randrange(1,4)
            table = tuple(tuple(rng.randrange(-1,n) for _ in range(2)) for _ in range(n))
            ms.append(BinaryDFA(table,frozenset(q for q in range(n) if rng.random()<.6),rng.randrange(n)))
        ms=tuple(ms)
        nodes=[(i,q) for i,m in enumerate(ms) for q in range(len(m.delta))]+[(r,0)]
        flags=frozenset((x,y) for x in nodes for y in nodes if rng.random()<.045)
        bad=frozenset(x for x in nodes if rng.random()<.015)
        sys=BlockSystem(ms,flags,bad)
        I,_=sys.compile()
        candidate=tuple(words('01',2 if r<4 else 1))
        found=False
        for blocks in itertools.product(candidate,repeat=r):
            w=encode_blocks(blocks)
            a=witness(I,w)
            assert a==border_witness(I,w)==block_witness(sys,blocks)
            counts['cyclic_tuples']+=1
            counts['formula_binary_comparisons']+=1
            found |= a
        answer=solve_blocks(sys,max_states=150000,max_transitions=1000000)
        counts['cyclic_instances']+=1
        cyclic_verdicts[answer['status']]+=1
        if found:
            assert answer['status']=='YES', (trial,answer)
        if answer['status']=='YES':
            assert block_witness(sys,answer['blocks'])
    # C048 equal-word construction is contained: put predecessor tags in the stage DFA.
    tagger=BinaryDFA(((1,2),(1,2),(1,2)),frozenset({0,1,2}))
    tag_flags=frozenset(((0,p),(1,q)) for p in range(3) for q in range(3) if p!=q)
    equality=BlockSystem((tagger,tagger),tag_flags)
    for u,v in itertools.product(tuple(words('01',3)),repeat=2):
        assert block_witness(equality,(u,v)) == (u==v)
        counts['formula_binary_comparisons']+=1
    samples.append(dict(name='whole_word_equality_subclass',result=solve_blocks(equality,max_states=None,max_transitions=None)))
    # C048 is a subcase, but the new decider takes arbitrary flags rather than
    # assuming equality. Cross-check every total two-state DFA pair against the
    # separate direct product solver.
    def tagged(m):
        n=len(m.delta)
        table=[]
        for q in (m.start,)+tuple(q for q in range(n) for _ in (0,1)):
            table.append(tuple(-1 if t<0 else 1+2*t+a for a,t in enumerate(m.delta[q])))
        finals={0} if m.start in m.final else set()
        finals.update(1+2*q+a for q in m.final for a in (0,1))
        return BinaryDFA(tuple(table),frozenset(finals))
    all_small=[]
    for entries in itertools.product(range(2),repeat=4):
        for mask in range(4):
            all_small.append(BinaryDFA((entries[:2],entries[2:]),frozenset(q for q in range(2) if mask>>q&1)))
    sync_verdicts={'YES':0,'NO':0,'UNKNOWN':0}
    tags=['START','0','1','0','1']
    fs=frozenset(((0,p),(1,q)) for p in range(5) for q in range(5) if tags[p]!=tags[q])
    for m,n in itertools.product(all_small,repeat=2):
        sys=BlockSystem((tagged(m),tagged(n)),fs)
        out=solve_blocks(sys,max_states=None,max_transitions=None)
        expected=solve_sync((m,n),max_states=None)
        assert out['status']==expected['status'], (m,n,out,expected)
        counts['independent_sync_decisions']+=1;sync_verdicts[out['status']]+=1
    impossible=BlockSystem((BinaryDFA(((1,-1),(-1,2),(-1,2)),frozenset({1,2})),
                            BinaryDFA(((-1,1),(-1,1)),frozenset({1}))),
                            frozenset({((0,1),(1,0)),((0,1),(1,1)),((0,2),(1,0))}))
    impossible_result=solve_blocks(impossible,max_states=None,max_transitions=None)
    assert impossible_result['status']=='NO'
    samples.append(dict(name='nonconvergent_necessary_family_decided',result=impossible_result))
    for sys in (fixture,single,equality):
        I,_=sys.compile()
        R=realize(I)
        for _ in range(6):
            blocks=tuple(rng.choice(('','0','1','01')) for _ in sys.automata)
            w=encode_blocks(blocks)
            expected=block_witness(sys,blocks)
            assert (not Canonical(R.variables,R.constraints,R.alpha,R.beta,w).errors())==expected
            counts['canonical_models']+=1
    results=dict(status='PASS',seed=2026090651,counts=counts,finite_language_oracles=finite_verdicts,dictionary_oracles=dictionary_verdicts,
                 cyclic_checks=cyclic_verdicts,sync_product_oracles=sync_verdicts,fixtures=samples,cap=cap,
                 necessary_hierarchy=incomplete_necessary_checks(),
                 proof_status='Written all-length arguments; not Lean-checked or independently reviewed',
                 scope='Exact supplied bounded-delimiter schema; no unrestricted decomposition theorem')
    path=ROOT/'results'/'delimited-blocks.json'
    path.write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))

if __name__=='__main__':
    main()
