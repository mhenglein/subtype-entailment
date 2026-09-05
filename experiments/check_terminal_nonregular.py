"""An actual nine-variable system with nonregular terminal separating paths.

Language: {0^m 1 0^(n+1) 1 : m,n>=0 and n>=m}.
The all-length proof is separate from these bounded exact-model checks.
"""
import json
from pathlib import Path
from border_lab import Instance, witness, border_witness, words
from terminal_realization import realize
from denial_bridge import build, Canonical

INSTANCE=Instance(((0,1),(2,-1),(2,3),(-1,-1)),
                  frozenset({3}),frozenset({(0,1)}))
ROOT=Path(__file__).resolve().parents[1]


def predicted(w):
    parts=w.split('1')
    return len(parts)==3 and parts[-1]=='' and len(parts[1])>len(parts[0])


def main():
    R=realize(INSTANCE)
    status,B=build(R.variables,R.constraints,R.alpha,R.beta)
    assert status=='SAT' and R.variables==9
    total=0; canonical=0
    for w in words('01',10):
        good=predicted(w)
        assert witness(INSTANCE,w)==border_witness(INSTANCE,w)==witness(B.instance,w)==good
        total+=1
        if len(w)<=7 or good:
            assert (not Canonical(R.variables,R.constraints,R.alpha,R.beta,w).errors())==good
            canonical+=1
    grid=0
    for m in range(21):
        for n in range(21):
            w='0'*m+'1'+'0'*(n+1)+'1'
            assert witness(INSTANCE,w)==(n>=m)
            assert border_witness(INSTANCE,w)==(n>=m)
            grid+=1
    # Pairwise distinguish the prefixes 0^a by suffix 1 0^(a+1) 1.
    separations=0
    for a in range(31):
        for b in range(a+1,31):
            suffix='1'+'0'*(a+1)+'1'
            assert witness(INSTANCE,'0'*a+suffix)
            assert not witness(INSTANCE,'0'*b+suffix)
            separations+=1
    out=dict(status='PASS',variables=R.variables,constraints=R.constraints,
             alpha=R.alpha,beta=R.beta,words_through_length_10=total,
             exact_canonical_model_checks=canonical,exponent_pairs=grid,
             distinguishability_pairs=separations,
             language='0^m 1 0^(n+1) 1, m,n>=0, n>=m',
             proof_status='Written proof of all-length characterization and nonregularity; not Lean-checked')
    (ROOT/'results/terminal-nonregular.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__': main()
