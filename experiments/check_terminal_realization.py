"""Independent bounded checks of the all-word terminal realization proof."""
import json
import random
from pathlib import Path
from border_lab import Instance, witness, border_witness, words, necessary, sufficient
from denial_bridge import build, reduced, Canonical
from terminal_realization import realize, terminal_restriction
from check_unrestricted_continuation import OBSTRUCTION

ROOT = Path(__file__).resolve().parents[1]


def main():
    rng = random.Random(2026090531)
    counts = {"instances": 0, "words": 0, "canonical_models": 0,
              "budget_predicates": 0, "summary_identities": 0,
              "terminal_restriction_words": 0}
    max_classes = 0
    fixtures = [
        Instance(((-1,-1),), frozenset({0})),
        Instance(((-1,-1),), frozenset()),
        Instance(((-1,-1),), frozenset({0}), frozenset({(0,0)})),
        Instance(((1,-1),(-1,-1)), frozenset({1}), frozenset({(0,1)})),
        Instance(((1,-1),(-1,-1)), frozenset({1}), bad=frozenset({1})),
        Instance(((-1,1),(-1,2),(2,3),(-1,-1)),frozenset({3}),frozenset({(0,1)})),
    ]
    for attempt in range(160):
        k = rng.randrange(1,7)
        final = frozenset(q for q in range(k) if rng.random() < .30)
        delta = tuple((-1,-1) if q in final else
                      tuple(rng.randrange(-1,k) for _ in range(2)) for q in range(k))
        flags = frozenset((q,r) for q in range(k) for r in range(k)
                          if rng.random() < (.04,.13,.30)[attempt%3])
        bad = frozenset(q for q in range(k) if rng.random()<.08)
        fixtures.append(Instance(delta,final,flags,bad,rng.randrange(k)))
    for index, I in enumerate(fixtures):
        R=realize(I)
        status, B=build(R.variables,R.constraints,R.alpha,R.beta)
        assert status=='SAT'
        J,cl=reduced(B,R.alpha,R.beta)
        assert J is not None
        k=len(I.delta); max_classes=max(max_classes,len(J.delta))
        counts['instances']+=1
        for w in words('01',5):
            counts['words']+=1
            good=witness(I,w)
            assert good==border_witness(I,w)==witness(B.instance,w)==witness(J,w),(index,w)
            run=I.run(w)
            if run is not None:
                q=run[-1]
                b_expected=frozenset({q}|{k+r for p,r in I.flags if p==q})
                a_expected=frozenset({k+q}|{p for p,r in I.flags if r==q})
                target=J.run(w)[-1]
                assert cl[target]==(b_expected,a_expected),(index,w,cl[target])
                counts['summary_identities']+=1
            for L,D in ((0,0),(1,0),(0,1),(1,1)):
                assert necessary(I,w,L,D)==necessary(J,w,L,D)
                assert sufficient(I,w,L,D)==sufficient(J,w,L,D)
                counts['budget_predicates']+=2
            # Exact regular model checks, not finite tree depth checks.
            if index<46 or good:
                actual=not Canonical(R.variables,R.constraints,R.alpha,R.beta,w).errors()
                assert actual==good,(index,w,'canonical')
                counts['canonical_models']+=1
    status,B=build(8,OBSTRUCTION)
    assert status=='SAT'
    I,_=reduced(B)
    T=terminal_restriction(I)
    R=realize(T)
    status,C=build(R.variables,R.constraints,R.alpha,R.beta)
    assert status=='SAT'
    for w in words('01',9):
        predicted=w.startswith('11') and w.endswith('1') and len(w)>=4 and set(w[2:-1])=={'0'}
        assert witness(T,w)==witness(C.instance,w)==predicted
        counts['terminal_restriction_words']+=1
    out=dict(status='PASS',seed=2026090531,counts=counts,
             maximum_reduced_summary_states=max_classes,
             proof_status='Written all-input proof, not Lean-checked',
             scope='Binary terminal-final abstract automata; arbitrary flags, Bad, and start',
             realization_variables='2*k+1',
             actual_obstruction=dict(original_summary_states=len(I.delta),
                                     realized_variables=R.variables,
                                     shortest_witness='1101',language='11 0^n 1, n>=1'))
    (ROOT/'results/terminal-realization.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__': main()
