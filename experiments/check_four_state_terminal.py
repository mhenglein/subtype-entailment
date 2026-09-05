"""Complete normalized four-state terminal-final census (finite-case evidence).

Normalize a chosen terminal final to 3 and start to 0, delete returns to the
initial state (prefix removal preserves witness and sufficient membership),
and absorb diagonal/final-column flags into state exclusions. Remaining
transitions target -1,1,2,3 and relevant flags are 0->1,0->2,1->2,2->1.
There are 4^6 * 16 = 65,536 normalized instances. Degenerate smaller cases
are handled by the same normalization and unused states.
"""
import argparse
import itertools
import json
from pathlib import Path
from border_lab import Instance,Sandwich,witness,border_witness,sufficient
ROOT=Path(__file__).resolve().parents[1]
PAIRS=((0,1),(0,2),(1,2),(2,1))


def run(start=0,stop=4096):
    counts={'instances':0,'YES':0,'NO':0,'UNKNOWN':0,'searches':0,
            'graph_cap_exits':0,'maximum_search_states':0}
    def search(machine):
        answer=machine.search(20000)
        counts['searches']+=1
        counts['maximum_search_states']=max(counts['maximum_search_states'],answer['states'])
        counts['graph_cap_exits']+=answer['status']=='UNKNOWN'
        return answer
    budget_counts={0:0,1:0,2:0}; max_len=0; worst=None; residual=[]
    for number,transitions in enumerate(itertools.product((-1,1,2,3),repeat=6)):
        if number<start:continue
        if number>=stop:break
        delta=tuple(tuple(transitions[2*q:2*q+2]) for q in range(3))+((-1,-1),)
        for mask in range(16):
            I=Instance(delta,frozenset({3}),frozenset(p for b,p in enumerate(PAIRS) if mask&(1<<b)))
            counts['instances']+=1; found=False
            # Low-budget N emptiness is already decisive; use it as a prefilter.
            nr=search(Sandwich(I,0,0))
            if nr['status']=='NO':counts['NO']+=1;continue
            for B in range(3):
                for L in range(B+1):
                    r=search(Sandwich(I,L,B-L,True))
                    if r['status']=='YES':
                        w=r['word'];assert witness(I,w) and border_witness(I,w) and sufficient(I,w,L,B-L)
                        counts['YES']+=1;budget_counts[B]+=1;found=True
                        if len(w)>max_len:max_len=len(w);worst={'delta':delta,'flags':sorted(I.flags),'word':w,'budget':B}
                        break
                if found:break
            if not found:
                nr=search(Sandwich(I,2,2))
                if nr['status']=='NO':counts['NO']+=1
                else:
                    counts['UNKNOWN']+=1
                    residual.append(dict(number=number,mask=mask,delta=delta,flags=sorted(I.flags),necessary=nr))
    return dict(status='PASS' if not residual else 'UNRESOLVED',transition_start=start,transition_stop=stop,
                counts=counts,first_successful_budget_counts=budget_counts,max_constructed_length=max_len,
                longest_returned=worst,residual=residual,
                scope='Exhaustive finite normalized census; audited Python graph certificates, not Lean proof',
                negative_budget=[2,2],state_cap_per_search=20000)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--start',type=int,default=0);p.add_argument('--stop',type=int,default=4096);a=p.parse_args()
    result=run(a.start,a.stop)
    name='four-state-terminal.json' if a.start==0 and a.stop==4096 else f'four-state-terminal-{a.start}-{a.stop}.json'
    (ROOT/'results'/name).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


def four_state_terminal_decision(instance):
    """Exact on <=4 terminal-final binary states, using the complete census.

    The global justification is the normalization proof plus the exhaustive
    finite graph certificates, not an assumption that bounded search suffices.
    Larger/nonterminal instances are outside this result and return UNKNOWN.
    """
    from terminal_realization import validate
    from border_lab import words
    validate(instance)
    if len(instance.delta)>4 or any(any(q>=0 for q in instance.delta[f]) for f in instance.final):
        return dict(status='UNKNOWN',reason='Outside four-state terminal class')
    for word in words('01',4):
        if witness(instance,word):
            assert border_witness(instance,word)
            return dict(status='YES',word=word)
    return dict(status='NO',reason='Complete four-state terminal classification')
