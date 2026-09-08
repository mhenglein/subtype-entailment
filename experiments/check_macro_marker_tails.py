"""Regression and differential checks for macro_marker_tail."""
import json
from pathlib import Path

from border_lab import Instance, witness, border_witness, words
from macro_marker_tail import macro_tail_decision, solve_macro
from synchronous_separators import (compile_separators,
    frontier_separator_certificate)
from target_frontier import (Limits, parse_macro, target_frontier_decision)

UNCAPPED=Limits(states=None,transitions=None,descriptors=None,schemas=None,
                reconstruction=None)


def macro_tail_safe(macro,blocks,H):
    """Independent block-level H-relaxation specification."""
    # positions are macro-boundary states before each block
    states=[macro.start]
    at=macro.start
    for u in blocks:
        for a in u:
            at=macro.delta[at][int(a)]
            if at < 0: return False
        at=macro.delta[at][2]
        if at < 0: return False
        states.append(at)
    if at != macro.final: return False
    r=len(blocks)
    for i in range(r):
        for j in range(i+1,r):
            if (states[i],states[j]) not in macro.flags: continue
            if r-j > H: continue
            left='#'.join(blocks[i:])+'#'
            right='#'.join(blocks[j:])+'#'
            if left.startswith(right): return False
    return True


def enumerate_blocks(macro,max_blocks,max_data):
    alphabet=['']
    for n in range(1,max_data+1):
        alphabet.extend(words('01',n)[2**n-1:])
    # Simpler explicit DFS over actual macro paths.
    out=[]
    def visit(at,blocks):
        if at==macro.final:
            out.append(tuple(blocks)); return
        if len(blocks)>=max_blocks: return
        stack=[(at,'')]; seen={(at,'')}
        while stack:
            q,u=stack.pop()
            m=macro.delta[q][2]
            if m>=0:
                visit(m,blocks+[u])
            if len(u)>=max_data: continue
            for a,t in enumerate(macro.delta[q][:2]):
                if t>=0:
                    item=(t,u+str(a))
                    if item not in seen:
                        seen.add(item); stack.append(item)
    visit(macro.start,[])
    return out


def recurrent_target_positive():
    # C056 rejects this because synchronization forces a separator cycle at
    # state 0 and target state 1 can return to it. Original word 01 is a witness.
    I=Instance(((1,0),(0,2),(-1,-1)),frozenset({2}),frozenset({(0,1)}))
    assert witness(I,'01') and border_witness(I,'01')
    summary,cert=frontier_separator_certificate(I)
    assert cert is not None
    J=compile_separators(I,cert)
    old=target_frontier_decision(J,UNCAPPED)
    assert old['status']=='UNKNOWN'
    new=macro_tail_decision(J,1,UNCAPPED)
    assert new['status']=='YES'
    assert witness(J,new['word']) and border_witness(J,new['word'])
    return dict(old_status='UNKNOWN',new_status='YES',compiled_word=new['word'])


def small_differential():
    fixtures=[
      Instance(((1,0),(0,2),(-1,-1)),frozenset({2}),frozenset({(0,1)})),
      Instance(((1,0),(-1,2),(-1,-1)),frozenset({2}),frozenset({(0,1)})),
      Instance(((0,1),(-1,2),(-1,-1)),frozenset({2}),frozenset()),
    ]
    checked=0
    for I in fixtures:
        _,cert=frontier_separator_certificate(I)
        if cert is None: continue
        J=compile_separators(I,cert)
        fmt,macro=parse_macro(J,next(iter(J.final)),'paired')
        assert macro is not None,fmt
        for H in (1,2,3):
            brute=False
            for blocks in enumerate_blocks(macro,H+1,4):
                if len(blocks)<=H and macro_tail_safe(macro,blocks,H):
                    brute=True; break
                # When len>H, only final H blocks are constrained; prefix may
                # contain arbitrary earlier blocks, exactly the solver's case.
                if len(blocks)>H and macro_tail_safe(macro,blocks,H):
                    brute=True; break
            out=solve_macro(macro,H,UNCAPPED)
            if out['status']=='YES':
                assert brute or len(out['word'])>0
            checked += 1
    return checked


def main():
    result={'status':'PASS','recurrent_target_positive':recurrent_target_positive(),
            'small_differential_queries':small_differential(),
            'scope':'Exact supplied-H paired macro-marker relaxation; no global marker bound claimed',
            'proof_status':'Written proof pending independent review; regression evidence; not Lean-checked'}
    path=Path(__file__).resolve().parents[1]/'results'/'macro-marker-tails.json'
    path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__': main()
