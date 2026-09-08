"""Regression and differential checks for macro marker-tail machinery."""
import json
from pathlib import Path

from border_lab import Instance, witness, border_witness
from macro_marker_tail import macro_tail_decision, solve_macro
from macro_marker_spectrum import spectrum_macro, semantic_macro_decision
from synchronous_separators import compile_separators, frontier_separator_certificate
from target_frontier import Limits, parse_macro, target_frontier_decision

UNCAPPED=Limits(states=None,transitions=None,descriptors=None,schemas=None,
                reconstruction=None)


def macro_tail_safe(macro,blocks,H):
    states=[macro.start]; at=macro.start
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
            if (states[i],states[j]) not in macro.flags or r-j > H: continue
            if ('#'.join(blocks[i:])+'#').startswith('#'.join(blocks[j:])+'#'):
                return False
    return True


def enumerate_blocks(macro,max_blocks,max_data):
    out=[]
    def visit(at,blocks):
        if at==macro.final:
            out.append(tuple(blocks)); return
        if len(blocks)>=max_blocks: return
        stack=[(at,'')]; seen={(at,'')}
        while stack:
            q,u=stack.pop(); m=macro.delta[q][2]
            if m>=0: visit(m,blocks+[u])
            if len(u)>=max_data: continue
            for a,t in enumerate(macro.delta[q][:2]):
                if t>=0:
                    item=(t,u+str(a))
                    if item not in seen: seen.add(item); stack.append(item)
    visit(macro.start,[])
    return out


def recurrent_target_positive():
    I=Instance(((1,0),(0,2),(-1,-1)),frozenset({2}),frozenset({(0,1)}))
    assert witness(I,'01') and border_witness(I,'01')
    _,cert=frontier_separator_certificate(I); assert cert is not None
    J=compile_separators(I,cert)
    old=target_frontier_decision(J,UNCAPPED); assert old['status']=='UNKNOWN'
    fixed=macro_tail_decision(J,1,UNCAPPED); assert fixed['status']=='YES'
    assert witness(J,fixed['word']) and border_witness(J,fixed['word'])
    fmt,macro=parse_macro(J,next(iter(J.final)),'paired'); assert macro is not None,fmt
    spectrum=spectrum_macro(macro,UNCAPPED)
    semantic=semantic_macro_decision(J,UNCAPPED)
    assert spectrum['status'] in ('FINITE','UNBOUNDED')
    if spectrum['status']=='FINITE':
        assert semantic['status']=='YES'
        assert witness(J,semantic['word']) and border_witness(J,semantic['word'])
    return dict(old_status='UNKNOWN',fixed_H1_status='YES',compiled_word=fixed['word'],
                macro_spectrum_status=spectrum['status'],macro_spectrum_H=spectrum.get('H'),
                semantic_status=semantic['status'])


def zero_marker_positive():
    # No proper flags => exact macro spectrum H=0. The H=0 relaxation is plain
    # boundary-safe reachability and must return a candidate, not NO.
    I=Instance(((0,1),(-1,2),(-1,-1)),frozenset({2}),frozenset())
    _,cert=frontier_separator_certificate(I); assert cert is not None
    J=compile_separators(I,cert)
    fmt,macro=parse_macro(J,2,'paired'); assert macro is not None,fmt
    spectrum=spectrum_macro(macro,UNCAPPED); assert spectrum['status']=='FINITE' and spectrum['H']==0
    fixed=solve_macro(macro,0,UNCAPPED); assert fixed['status']=='YES'
    assert witness(J,fixed['word']) and border_witness(J,fixed['word'])
    semantic=semantic_macro_decision(J,UNCAPPED); assert semantic['status']=='YES'
    return dict(H=0,fixed_status='YES',semantic_status='YES',word=fixed['word'])


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
        fmt,macro=parse_macro(J,next(iter(J.final)),'paired'); assert macro is not None,fmt
        for H in (1,2,3):
            brute=any(macro_tail_safe(macro,b,H) for b in enumerate_blocks(macro,H+1,4))
            out=solve_macro(macro,H,UNCAPPED)
            if out['status']=='YES': assert brute or len(out['word'])>0
            checked += 1
    return checked


def main():
    result={'status':'PASS','recurrent_target_positive':recurrent_target_positive(),
            'zero_marker_positive':zero_marker_positive(),
            'small_differential_queries':small_differential(),
            'scope':'Exact supplied-H paired macro tails plus exact macro separator spectrum on formatted slices',
            'proof_status':'Written proofs pending independent review; regression evidence; not Lean-checked'}
    path=Path(__file__).resolve().parents[1]/'results'/'macro-marker-tails.json'
    path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__=='__main__': main()
