"""Reproducible tests of fixed-skeleton formulas and complete flat covers.

SMT results use an optional external arithmetic backend. Timeouts are UNKNOWN.
Formula construction and flat-cover completeness have separate written proofs.
"""
import itertools
import json
import random
import subprocess
import sys
from pathlib import Path
from border_lab import Instance,witness,border_witness,words
from skeleton_presburger import Skeleton
from flat_terminal import flat_schemas,decide_flat_terminal
from check_terminal_nonregular import INSTANCE
ROOT=Path(__file__).resolve().parents[1]


def batch_fixed(cases,timeout_ms=1000):
    scripts=[]; expected=[]
    for I,blocks,values in cases:
        S=Skeleton(I,blocks);word=S.expand(values)
        expected.append(witness(I,word))
        assert expected[-1]==border_witness(I,word)
        scripts.append('(reset)\n'+S.script(values=values,timeout_ms=timeout_ms,engine='smt'))
    run=subprocess.run([sys.executable,str(Path(__file__).with_name('_z3_native.py'))],
                       input='\n'.join(scripts),text=True,capture_output=True,timeout=30)
    if run.returncode or '(error' in run.stdout:
        raise RuntimeError(run.stdout+run.stderr)
    verdicts=[line.strip() for line in run.stdout.splitlines() if line.strip() in ('sat','unsat','unknown')]
    assert len(verdicts)==len(expected),(len(verdicts),len(expected),run.stdout)
    for index,(verdict,good) in enumerate(zip(verdicts,expected)):
        assert verdict=='unknown' or (verdict=='sat')==good,(index,verdict,good)
    return {key:verdicts.count(key) for key in ('sat','unsat','unknown')}


def schemas_words(schemas,bound):
    result=set()
    for blocks in schemas:
        r=sum(b.repeat for b in blocks)
        for ns in itertools.product(range(bound+1),repeat=r):
            exponents=iter(ns);word=''.join(b.word*(next(exponents) if b.repeat else 1) for b in blocks)
            if len(word)<=bound:result.add(word)
    return result


def main():
    rng=random.Random(2026090533)
    cases=[]
    # Two independent stars and zero counts; exact relation n1>=n0.
    blocks=[('0',True),('10',False),('0',True),('1',False)]
    for m in range(5):
        for n in range(5):cases.append((INSTANCE,blocks,[m,n]))
    # The repeated word need not be a loop: its DFA action alternates states.
    parity=Instance(((1,-1),(0,2),(-1,-1)),frozenset({2}))
    for n in range(8):cases.append((parity,[('0',True),('1',False)],[n]))
    # Regression of the exact pre-final-loop obstruction: n=0 is NOT a witness.
    obstruction=Instance(((-1,1),(-1,2),(2,3),(-1,-1)),frozenset({3}),frozenset({(0,1)}))
    for n in range(5):cases.append((obstruction,[('11',False),('0',True),('1',False)],[n]))
    for attempt in range(42):
        k=rng.randrange(1,5)
        I=Instance(tuple(tuple(rng.randrange(-1,k) for _ in range(2)) for _ in range(k)),
                   frozenset(q for q in range(k) if rng.random()<.5),
                   frozenset((q,r) for q in range(k) for r in range(k) if rng.random()<.15),
                   frozenset(q for q in range(k) if rng.random()<.08),rng.randrange(k))
        b=[(''.join(rng.choice('01') for _ in range(rng.randrange(3))),False),
           (rng.choice(('0','1','01','10','001')),True),
           (''.join(rng.choice('01') for _ in range(rng.randrange(3))),False)]
        for n in range(3):cases.append((I,b,[n]))
    batches=[]
    for start in range(0,len(cases),40):batches.append(batch_fixed(cases[start:start+40]))
    counts={key:sum(b[key] for b in batches) for key in ('sat','unsat','unknown')}
    cover_count=0; comparisons=0; tested=[]
    no=Instance(((-1,1),(1,2),(-1,-1)),frozenset({2}),frozenset({(0,1)}))
    for I in (INSTANCE,obstruction,no,parity):
        cover=flat_schemas(I);assert cover['status']=='COMPLETE'
        generated=schemas_words(cover['schemas'],10)
        safe_bad=I.bad|frozenset(p for p,q in I.flags if p==q)
        for w in words('01',10):
            run=I.run(w)
            accepted=run is not None and run[-1] in I.final and not (safe_bad&set(run))
            assert (w in generated)==accepted
            comparisons+=1
        cover_count+=len(cover['schemas'])
        result=decide_flat_terminal(I,timeout_ms=1500)
        tested.append(result)
    # Genuine unbounded query, not exponent enumeration. Large counts requested
    # only to demonstrate that the algorithm does not impose a small cutoff.
    S=Skeleton(INSTANCE,blocks)
    unbounded=S.solve(extra='(and (>= n0 25) (= n0 n1))',timeout_ms=2500)
    assert unbounded['status']=='YES'
    nonflat=Instance(((1,-1),(1,2),(1,3),(-1,-1)),frozenset({3}))
    guard=decide_flat_terminal(nonflat)
    assert guard['status']=='UNKNOWN' and guard['reason']=='Nonflat productive SCC'
    out=dict(status='PASS',seed=2026090533,fixed_exponent_formula_cases=len(cases),
             formula_verdicts=counts,flat_schemas_checked=cover_count,
             flat_language_membership_comparisons=comparisons,
             unbounded_solver_fixtures=tested,large_unbounded_query=unbounded,
             nonflat_guard=guard,backend='Z3 4.13.3.0 shared library (optional)',
             proof_status='Written Presburger translation and flat-cover proof; no Lean or solver proof certificate',
             limitations='Bounded regressions are not the proof. Timeouts remain UNKNOWN; negatives require two backend entry points.')
    (ROOT/'results/terminal-arithmetic.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
