"""E034: independently check the raw bounded-marker recognition/cover front end."""
import itertools
import json
import random
from pathlib import Path
from border_lab import Instance, witness, border_witness, words
from word_sync import BinaryDFA, compile_sync, solve_sync
from delimited_blocks import BlockSystem, solve_blocks
from marker_certificate import marker_decision, marker_structure

ROOT = Path(__file__).resolve().parents[1]


def compile_macro(table, final, flags=frozenset(), bad=frozenset(), start=0):
    """Independent direct expansion of a three-letter macro DFA (0,1,#)."""
    n = len(table)
    D = [[-1, -1] for _ in range(3*n)]
    for q, (zero, one, sep) in enumerate(table):
        if zero >= 0 or one >= 0:
            D[3*q][1] = 3*q+1
            D[3*q+1] = [3*zero if zero >= 0 else -1, 3*one if one >= 0 else -1]
        if sep >= 0:
            D[3*q][0] = 3*q+2
            D[3*q+2][0] = 3*sep
    return Instance(tuple(map(tuple, D)), frozenset({3*final}),
                    frozenset((3*p, 3*q) for p, q in flags),
                    frozenset(3*q for q in bad), 3*start)


def all_acyclic_paths(I):
    assert all(t < 0 or t > q for q, row in enumerate(I.delta) for t in row)
    pending = [('', I.start)]
    out = []
    while pending:
        w, q = pending.pop()
        if q in I.final:
            out.append(w)
        for a, t in enumerate(I.delta[q]):
            if t >= 0:
                pending.append((w+str(a), t))
    return out


def check():
    rng = random.Random(2026090653)
    counts = dict(acyclic_instances=0, complete_candidate_words=0,
                  cyclic_schema_instances=0, cyclic_product_instances=0,
                  mismatches=0, format_guards=0, cap_guards=0)
    stats = {name:{s:0 for s in ('YES','NO','UNKNOWN')}
             for name in ('acyclic','cyclic_schemas','cyclic_products')}
    for _ in range(400):
        n = rng.randrange(2, 8)
        table = []
        for q in range(n-1):
            later = list(range(q+1, n-1))
            table.append((rng.choice([-1]+later), rng.choice([-1]+later),
                          rng.choice([-1]+list(range(q+1,n)))))
        table.append((-1,-1,-1))
        G=frozenset((p,q) for p in range(n) for q in range(n) if rng.random()<.05)
        bad=frozenset(q for q in range(n) if rng.random()<.02)
        I=compile_macro(tuple(table),n-1,G,bad)
        candidates=all_acyclic_paths(I)
        good=[]
        for w in candidates:
            yes=witness(I,w)
            assert yes==border_witness(I,w)
            counts['complete_candidate_words']+=1
            if yes:good.append(w)
        out=marker_decision(I,max_schemas=None,max_states=None,max_transitions=None)
        assert out['status']!='UNKNOWN' and (out['status']=='YES')==bool(good),(I,out,good)
        counts['acyclic_instances']+=1;stats['acyclic'][out['status']]+=1
    for _ in range(160):
        r=rng.randrange(1,4)
        ms=[]
        for i in range(r):
            n=rng.randrange(1,4)
            ms.append(BinaryDFA(tuple(tuple(rng.randrange(-1,n) for a in range(2)) for q in range(n)),
                                frozenset(q for q in range(n) if rng.random()<.65)))
        nodes=[(i,q) for i,m in enumerate(ms) for q in range(len(m.delta))]+[(r,0)]
        G=frozenset((p,q) for p in nodes for q in nodes if rng.random()<.03)
        S=BlockSystem(tuple(ms),G)
        I,_=S.compile()
        expected=solve_blocks(S,max_states=None,max_transitions=None)
        out=marker_decision(I,max_schemas=None,max_states=None,max_transitions=None)
        assert expected['status']==out['status'] and out['status']!='UNKNOWN',(S,out,expected)
        counts['cyclic_schema_instances']+=1;stats['cyclic_schemas'][out['status']]+=1
    for _ in range(120):
        ms=[]
        for i in range(rng.randrange(2,4)):
            n=rng.randrange(1,4)
            ms.append(BinaryDFA(tuple(tuple(rng.randrange(-1,n) for a in range(2)) for q in range(n)),
                                frozenset(q for q in range(n) if rng.random()<.55)))
        F=compile_sync(ms)
        expected=solve_sync(ms,max_states=None)
        out=marker_decision(F.instance,max_schemas=None,max_states=None,max_transitions=None)
        assert expected['status']==out['status'] and out['status']!='UNKNOWN',(out,expected)
        counts['cyclic_product_instances']+=1;stats['cyclic_products'][out['status']]+=1

    # The actual five-state obstruction, without inserting or encoding a marker.
    I=Instance(((2,1),(2,1),(-1,3),(4,3),(-1,-1)),frozenset({4}),
               frozenset({(0,2),(0,3),(1,2)}))
    no=marker_decision(I,max_schemas=None,max_states=None,max_transitions=None)
    assert no['status']=='NO' and no['slices'][0]['certificate']['code']=='unary'

    # Variable separator count, multiple complete schemas, and nonflat data SCCs.
    table=((1,2,-1),(1,1,5),(2,2,3),(3,3,5),(-1,-1,-1),(-1,-1,-1))
    variable=compile_macro(table,5)
    var=marker_decision(variable,max_schemas=None,max_states=None,max_transitions=None)
    assert var['status']=='YES'
    # A productive separator cycle may not be treated as a finite cover.
    cyclic_marker=compile_macro(((0,1,0),(1,1,2),(-1,-1,-1)),2)
    cy=marker_decision(cyclic_marker)
    assert cy['status']=='UNKNOWN';counts['format_guards']+=1
    # Safe accepted words outside either supported token format are not discarded.
    irregular=Instance(((1,-1),(-1,2),(-1,-1)),frozenset({2})) # only 01
    ir=marker_decision(irregular)
    assert ir['status']=='UNKNOWN';counts['format_guards']+=1
    U=BinaryDFA(((0,0),),frozenset({0}))
    odd,_=BlockSystem((U,U)).compile()
    odd=Instance(odd.delta,odd.final,frozenset({(1,3)}))
    og=marker_decision(odd)
    assert og['status']=='UNKNOWN';counts['format_guards']+=1
    nonterminal=Instance(((0,0),),frozenset({0}))
    assert marker_decision(nonterminal)['status']=='UNKNOWN';counts['format_guards']+=1
    assert marker_decision(Instance(((-1,-1),),frozenset({0})))['word']==''
    cap=marker_decision(BlockSystem((U,U,U),frozenset({((0,0),(1,0))})).compile()[0],max_states=1)
    assert cap['status']=='UNKNOWN';counts['cap_guards']+=1
    # All short words still cross-check the independent binary predicates.
    for fixture in (I,variable,cyclic_marker,irregular,odd):
        for w in words('01',8):
            assert witness(fixture,w)==border_witness(fixture,w)
    return dict(status='PASS',seed=2026090653,counts=counts,verdicts=stats,
                five_state_hierarchy_obstruction=no,variable_marker_fixture=var,
                explicit_guards=dict(cyclic_markers=cy,outside_format=ir,odd_flags=og,capped=cap),
                proof_status='Written certificate and complete-cover argument; not Lean checked',
                scope='Certified bounded-marker raw inputs only; UNKNOWN outside this class')


if __name__=='__main__':
    out=check()
    (ROOT/'results/marker-certificate.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
