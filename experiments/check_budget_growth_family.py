"""A two-parameter exact-budget family, including B=2k-4 on k states.

The all-length proof is independent of the finite searches below. See
notes/2026-09-04-budget-growth-family.md. Standard library only.
"""
from dataclasses import replace
import json
from continue_research import budgets,encode,ROOT
from border_lab import Instance,witness,border_witness,word_budget,words,sufficient


def family(m:int,t:int)->Instance:
    """States 0..m, final m, 0-chain then loop, m --1--> 1, flag (0,t)."""
    if not isinstance(m,int) or not isinstance(t,int) or not (m>=2 and 1<=t<m):
        raise ValueError('Require integers m>=2 and 1<=t<m.')
    return Instance(tuple([(q+1,-1) for q in range(m)]+[(m,1)]),
                    frozenset({m}),frozenset({(0,t)}))


def main():
    rows=[]; comparisons=0
    for m in range(2,9):
        baseline=budgets(replace(family(m,1),flags=frozenset()),m-1)
        assert baseline['status']=='EXACT' and baseline['budget']==m-1
        for t in range(1,m):
            I=family(m,t)
            expected='0'*m+'1'+'0'*(m+t)
            B=m+t-1
            result=budgets(I,B)
            assert result['status']=='EXACT' and result['budget']==B
            assert witness(I,expected) and border_witness(I,expected)
            assert sufficient(I,expected,B,0) and word_budget(I,expected)==B
            assert result['word']==expected
            brute=None
            if m<=5:
                count=0
                for w in words('01',len(expected)):
                    count+=1; comparisons+=1
                    f=witness(I,w)
                    assert f==border_witness(I,w)
                    if f:
                        assert w==expected
                        brute=dict(word=w,length=len(w),words_scanned_to_first=count)
                        break
                assert brute is not None
            rows.append(dict(m=m,t=t,states=m+1,instance=encode(I),
                             theoretical_budget=B,theoretical_shortest_length=2*m+t+1,
                             theoretical_boundary_budget=m-1,
                             result=result,shortest_bruteforce=brute))
    out=dict(status='PASS',parameter_pairs=len(rows),rows=rows,
             direct_shortest_word_comparisons=comparisons,
             global_claim='Written proof for every m>=2 and 1<=t<m; finite automaton replay for m=2..8.',
             strongest_subfamily='t=m-1: k=m+1 states, B=2k-4, shortest length=3k-3, boundary budget=k-2',
             state_cap_per_split=200000,
             unknown_results=0)
    (ROOT/'results/budget-growth-family.json').write_text(json.dumps(out,indent=2)+'\n')
    print('Exact family:',len(rows),'parameter pairs PASS;',comparisons,'direct shortest-word comparisons')
    for row in rows:
        if row['t']==row['m']-1:
            print('k=%s B=%s shortest=%s boundary=%s' %
                  (row['states'],row['theoretical_budget'],row['theoretical_shortest_length'],row['theoretical_boundary_budget']))

if __name__=='__main__': main()
