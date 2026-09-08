"""A017 reproducible regression. See the linked research note for exact scope.

In a full repo import the previous monoid solver normally. In this partial
snapshot, replace ONLY its missing input-validator import after checking its
Git blob hash. The comparison algorithm remains the original source.
"""
import ast
from collections import Counter, deque
from dataclasses import replace
import hashlib
from itertools import product
import json
from pathlib import Path
import random
import time
from border_lab import Instance, witness, border_witness, words
from regular_family_orbits import check_regular_family_orbits as orbit
from regular_family_orbits import validate_binary, intersection_instance, encode_blocks
ROOT=Path(__file__).resolve().parents[1]
SEED=2026090701

def old_backend():
    try:
        from regular_family_safety import check_regular_family
        return check_regular_family,'Full repository import'
    except ModuleNotFoundError as error:
        if error.name!='shared_word_templates':raise
    path=ROOT/'experiments/regular_family_safety.py'; blob=path.read_bytes()
    assert hashlib.sha1(b'blob '+str(len(blob)).encode()+b'\0'+blob).hexdigest()=='4ea63af0bb20772ba8902df2aad8138ccbf6a568'
    tree=ast.parse(blob,filename=str(path))
    tree.body=[n for n in tree.body if not(isinstance(n,ast.ImportFrom) and n.module=='shared_word_templates')]
    ns={'validate_instance':validate_binary}
    exec(compile(tree,str(path),'exec'),ns)
    return ns['check_regular_family'],'Hash-verified snapshot; validator import substituted only'

def dictionary(entries):
    rows=[{}]; finals=set()
    for word in entries:
        q=0
        for a in word:
            if a not in rows[q]:rows[q][a]=len(rows);rows.append({})
            q=rows[q][a]
        finals.add(q)
    return Instance(tuple(tuple(row.get(a,-1) for a in '01') for row in rows),frozenset(finals))

def intersection_word(automata):
    start=tuple(A.start for A in automata); todo=deque([start]); paths={start:''}
    while todo:
        node=todo.popleft()
        if all(q in A.final for q,A in zip(node,automata)):return paths[node]
        for a in (0,1):
            nxt=tuple(A.delta[q][a] for q,A in zip(node,automata))
            if all(q>=0 for q in nxt) and nxt not in paths:
                paths[nxt]=paths[node]+str(a);todo.append(nxt)
    return None

def run():
    started=time.monotonic();rng=random.Random(SEED);old,harness=old_backend()
    counts=Counter();outcomes=Counter()
    def compare(I,D,capped=False):
        new=orbit(I,D,50000 if capped else None,10000 if capped else None)
        prev=old(I,D,5000 if capped else None,1000000 if capped else None)
        if 'UNKNOWN' in (new['status'],prev['status']):counts['capped_comparisons_unknown']+=1
        else:
            assert new['status']==prev['status'],(I,D,new,prev)
            if new['status']=='REGULAR_FAMILY_VALID':assert new['inhabited']==prev['inhabited']
            counts['exact_backend_agreements']+=1
        outcomes[new['status']]+=1
        if new['status']=='COUNTEREXAMPLE':
            w=new['word'];assert D.admissible(w) and not witness(I,w) and not border_witness(I,w)
            counts['independently_checked_counterexamples']+=1
        return new
    fs=list(product(range(2),repeat=2))
    for cells in product(range(-1,2),repeat=4):
        for f,g,b,s in product(range(4),range(16),range(4),range(2)):
            I=Instance((cells[:2],cells[2:]),frozenset(q for q in range(2) if f>>q&1),
                       frozenset(pair for j,pair in enumerate(fs) if g>>j&1),
                       frozenset(q for q in range(2) if b>>q&1),s)
            compare(I,replace(I,flags=frozenset(),bad=frozenset()))
            counts['exhaustive_two_state_instances']+=1
    print('two-state census passed',flush=True)
    for cells in product(range(-1,3),repeat=4):
        for flags in ({(0,1)},{(1,0)},{(0,1),(1,0)},{(0,2)}):
            I=Instance((cells[:2],cells[2:],(-1,-1)),frozenset({2}),frozenset(flags))
            compare(I,replace(I,flags=frozenset()));counts['three_state_terminal_cases']+=1
    for _ in range(400):
        k=rng.choice((3,4))
        I=Instance(tuple(tuple(rng.randrange(-1,k) for _ in range(2)) for _ in range(k)),
                   frozenset(q for q in range(k) if rng.randrange(2)),
                   frozenset((p,q) for p in range(k) for q in range(k) if rng.randrange(7)==0),
                   frozenset(q for q in range(k) if rng.randrange(15)==0),rng.randrange(k))
        if rng.randrange(2):D=replace(I,flags=frozenset(),bad=frozenset())
        else:
            n=rng.choice((1,2))
            D=Instance(tuple(tuple(rng.randrange(-1,n) for _ in range(2)) for _ in range(n)),
                       frozenset(q for q in range(n) if rng.randrange(2)))
        got=compare(I,D,True)
        for w in words('01',7):
            if D.admissible(w):
                assert witness(I,w)==border_witness(I,w)
                if got['status']=='REGULAR_FAMILY_VALID':assert witness(I,w)
                counts['bounded_domain_word_checks']+=1
        counts['seeded_mixed_domain_cases']+=1
    short=list(words('01',2))
    for _ in range(160):
        k=rng.randrange(1,5)
        I=Instance(tuple(tuple(rng.randrange(-1,k) for _ in range(2)) for _ in range(k)),
                   frozenset(q for q in range(k) if rng.randrange(2)),
                   frozenset((p,q) for p in range(k) for q in range(k) if rng.randrange(5)==0))
        chosen=set(rng.sample(short,rng.randrange(0,5)));D=dictionary(chosen);got=compare(I,D)
        assert (got['status']=='REGULAR_FAMILY_VALID')==all(witness(I,w) for w in chosen)
        assert got.get('inhabited',bool(chosen))==bool(chosen)
        counts['complete_finite_family_oracles']+=1;counts['complete_finite_family_words']+=len(chosen)
    recurrent=Instance(((-1,1),(2,1),(2,3),(4,3),(-1,-1)),frozenset({4}),frozenset({(0,3),(1,2)}))
    safe=Instance(((-1,1),(2,-1),(2,3),(4,-1),(-1,-1)),frozenset({4}))
    examples={'infinite_recurrent_safe':compare(recurrent,safe),
              'infinite_recurrent_mixed':compare(recurrent,replace(recurrent,flags=frozenset())),
              'nonterminal_no_flags':compare(Instance(((0,0),),frozenset({0})),Instance(((0,0),),frozenset({0})))}
    assert examples['infinite_recurrent_safe']['status']=='REGULAR_FAMILY_VALID'
    assert examples['infinite_recurrent_mixed']['status']=='COUNTEREXAMPLE'
    assert witness(recurrent,'1010')
    for n in range(1,10):
        I=Instance(tuple((q+1,-1) if q<n else (-1,-1) for q in range(n+1)),frozenset({n}),frozenset({(0,1)}))
        got=compare(I,replace(I,flags=frozenset()));assert got['word']=='0'*n
        counts['sharp_terminal_unary_cases']+=1
    print('backend, finite-family, and analytic checks passed',flush=True)
    reduction_results=[]
    for case in range(100):
        r=rng.choice((2,3));sets=[set(rng.sample(short,rng.randrange(0,4))) for _ in range(r)]
        automata=[dictionary(s) for s in sets];I,D=intersection_instance(automata)
        common=intersection_word(automata);bad_words=[];expected=set()
        for block_tuple in product(*[sorted(s) for s in sets]):
            w=encode_blocks(block_tuple);expected.add(w);c=I.run(w)
            assert I.admissible(w) and len(I.flags)==1
            source,target=next(iter(I.flags));assert c.count(source)==1 and c.count(target)==1
            bad=not witness(I,w);assert bad==(len(set(block_tuple))==1)
            assert witness(I,w)==border_witness(I,w)
            if bad:bad_words.append(w)
            counts['reduction_complete_candidate_words']+=1
        assert bool(bad_words)==(common is not None)
        if common is not None:assert not witness(I,encode_blocks([common]*r))
        for _ in range(40):
            w=''.join(rng.choice('01') for _ in range(rng.randrange(0,25)))
            assert I.admissible(w)==(w in expected);counts['reduction_raw_word_checks']+=1
        counts['complete_reduction_instances']+=1
        reduction_results.append(dict(blocks=r,input_states=sum(len(A.delta) for A in automata),
                                      output_states=len(I.delta),intersection_nonempty=common is not None))
    allwords=Instance(((0,0),),frozenset({0}));I,D=intersection_instance([allwords,allwords])
    examples['infinite_one_flag_reduction']=compare(I,D)
    for cap in ({'max_nodes':1,'max_chains':None},{'max_nodes':None,'max_chains':1}):
        got=orbit(I,D,**cap);assert got['status']=='UNKNOWN',got;counts['intentional_cap_regressions']+=1
    for invalid in (0,-1,True,1.5):
        try:orbit(I,D,max_nodes=invalid)
        except ValueError:counts['invalid_cap_regressions']+=1
        else:raise AssertionError('Invalid cap accepted')
    result=dict(seed=SEED,base_commit='f663a8d1072fbf21e899f860cba1538a64f3628a',status='PASS',
                seconds=round(time.monotonic()-started,3),comparison_harness=harness,counts=dict(counts),
                outcomes=dict(outcomes),examples=examples,reduction_instances=reduction_results,
                limits=['Written proof; no independent review or Lean formalization',
                        'Explicit BFS backend is not claimed polynomial-space',
                        'No unrestricted witness-existence or subtype decision',
                        'No full-repository CI from partial snapshot'])
    (ROOT/'results').mkdir(exist_ok=True)
    (ROOT/'results/regular-family-orbits.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('examples','reduction_instances')},indent=2))
    return result
if __name__=='__main__':run()
