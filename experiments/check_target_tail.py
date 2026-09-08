"""E036: exact target-local certificates and finite prefix-monitor pumping.

Independent finite-language oracles and a special cyclic family are separate
from positive-word tests. Resource caps never mean unrestricted NO.
"""
import itertools
import json
import random
from pathlib import Path
from border_lab import Instance, words, witness, border_witness
from word_sync import encode_blocks
from marker_certificate import marker_decision
from target_tail import target_tail_decision, target_tail_certificate, pump_witness
from run_normalization import profile_direct
from check_marker_certificate import compile_macro, all_acyclic_paths
from terminal_realization import realize
from denial_bridge import Canonical
ROOT=Path(__file__).resolve().parents[1]


def check():
    rng=random.Random(2026090656)
    counts=dict(acyclic_instances=0,acyclic_candidates=0,cyclic_family_instances=0,
                cyclic_oracle_words=0,known_witness_pumps=0,strict_pumps=0,
                known_positive_decisions=0,canonical_models=0,unsupported_guards=0,
                caps=0,independent_word_comparisons=0)
    verdicts={name:{s:0 for s in ('YES','NO','UNKNOWN')} for name in ('acyclic','cyclic_family','known_positive')}
    for _ in range(120):
        n=rng.randrange(2,7);table=[]
        for q in range(n-1):
            later=list(range(q+1,n-1))
            table.append((rng.choice([-1]+later),rng.choice([-1]+later),rng.choice([-1]+list(range(q+1,n)))))
        table.append((-1,-1,-1))
        flags=frozenset((p,q) for p in range(n) for q in range(n) if rng.random()<.06)
        I=compile_macro(tuple(table),n-1,flags);good=False
        for w in all_acyclic_paths(I):
            a=witness(I,w);assert a==border_witness(I,w)
            good |= a;counts['acyclic_candidates']+=1
        result=target_tail_decision(I,max_prefixes=None,max_states=None,max_transitions=None)
        assert result['status']!='UNKNOWN' and (result['status']=='YES')==good
        counts['acyclic_instances']+=1;verdicts['acyclic'][result['status']]+=1
    # Candidates are empty blocks followed by two one-letter blocks. Deleting
    # all empty prefix blocks only removes profile pairs, so the four no-prefix
    # candidates form a complete existence oracle for all tested flag subsets.
    table=((1,1,0),(-1,-1,2),(3,3,-1),(-1,-1,4),(-1,-1,-1))
    possible_flags=tuple((p,q) for p in range(4) for q in (2,3))
    extra_repetitions_checked=0;strict_extension_example=None
    for mask in range(1<<len(possible_flags)):
        flags=frozenset(p for bit,p in enumerate(possible_flags) if mask>>bit&1)
        I=compile_macro(table,4,flags);good=False
        for a,b in itertools.product('01',repeat=2):
            base=encode_blocks((a,b));base_profile=profile_direct(I,base)
            good |= witness(I,base);counts['cyclic_oracle_words']+=1
            for repetitions in (1,2,7):
                w=encode_blocks(('',)*repetitions+(a,b))
                assert base_profile <= profile_direct(I,w)
                assert witness(I,w)==border_witness(I,w)
                extra_repetitions_checked+=1
        result=target_tail_decision(I,max_prefixes=None,max_states=None,max_transitions=None)
        assert result['status']!='UNKNOWN' and (result['status']=='YES')==good,(flags,result,good)
        verdicts['cyclic_family'][result['status']]+=1;counts['cyclic_family_instances']+=1
        if flags and strict_extension_example is None and result['status']=='NO':
            old=marker_decision(I)
            assert old['status']=='UNKNOWN'
            strict_extension_example=dict(delta=I.delta,flags=sorted(I.flags),old_status=old['status'],new=result)
    macro=((0,1,0),(0,2,0),(2,2,3),(4,4,-1),(4,4,5),(5,5,6),(-1,-1,-1))
    I=compile_macro(macro,6,frozenset({(0,3)}))
    blocks=('0','10','1','11','0','1');w=encode_blocks(blocks)
    unsafe=encode_blocks(blocks[:1]+blocks[2:])
    assert witness(I,w) and not witness(I,unsafe)
    old=marker_decision(I);result=target_tail_decision(I,max_prefixes=3000)
    assert old['status']=='UNKNOWN' and result['status']=='YES'
    pumped=pump_witness(I,w,2);assert pumped['deleted_blocks']>0
    cert,_,_=target_tail_certificate(I,next(iter(I.final)))
    assert cert['status']=='CERTIFIED' and cert['target_height']==2
    context=dict(original=w,unsafe_single_deletion=unsafe,old_status=old['status'],new=result,pump=pumped,certificate=cert)
    for _ in range(140):
        prefix=tuple(rng.choice(('','0','1','10')) for _ in range(rng.randrange(3,25)))
        tail1=rng.choice(('0','1','00','01','10','11'));tail2=rng.choice(('','0','1','01','10'))
        blocks=prefix+('11',tail1,tail2);blank=compile_macro(macro,6)
        w=encode_blocks(blocks);P=profile_direct(blank,w)
        flags=frozenset((p,q) for p in range(6) for q in (3,4,5) if (3*p,3*q) not in P and rng.random()<.6)
        J=compile_macro(macro,6,flags)
        assert witness(J,w) and border_witness(J,w)
        out=pump_witness(J,w,2)
        assert out['retained_blocks']<=len(blocks)
        assert witness(J,out['word']) and border_witness(J,out['word'])
        counts['known_witness_pumps']+=1;counts['strict_pumps']+=out['deleted_blocks']>0
        if counts['known_witness_pumps']<=25:
            answer=target_tail_decision(J,max_prefixes=5000)
            assert answer['status']!='NO'
            if answer['status']=='YES':assert witness(J,answer['word'])
            verdicts['known_positive'][answer['status']]+=1;counts['known_positive_decisions']+=1
    five=Instance(((2,1),(2,1),(-1,3),(4,3),(-1,-1)),frozenset({4}),frozenset({(0,2),(0,3),(1,2)}))
    five_result=target_tail_decision(five,max_prefixes=None,max_states=None,max_transitions=None)
    assert five_result['status']=='NO'
    badcycle=compile_macro(macro,6,frozenset({(0,1)}))
    badcert,_,_=target_tail_certificate(badcycle,next(iter(badcycle.final)))
    assert badcert['status']=='NOT_APPLICABLE';counts['unsupported_guards']+=1
    irregular=Instance(((1,-1),(-1,2),(-1,-1)),frozenset({2}))
    assert target_tail_decision(irregular)['status']=='UNKNOWN';counts['unsupported_guards']+=1
    cap=target_tail_decision(I,max_prefixes=1)
    assert cap['status']=='UNKNOWN';counts['caps']+=1
    try:
        pump_witness(I,context['original'],1)
        raise AssertionError('Insufficient protected tail was not rejected')
    except ValueError:counts['unsupported_guards']+=1
    odd=Instance(I.delta,I.final,frozenset({(1,9)}),start=I.start)
    odd_word=context['original'];assert witness(odd,odd_word)
    try:
        pump_witness(odd,odd_word,2)
        raise AssertionError('Unaligned flag guard missing')
    except ValueError:counts['unsupported_guards']+=1
    for J in (I,five):
        R=realize(J)
        check_words=(context['original'],context['unsafe_single_deletion'],context['pump']['word']) if J==I else ('010','10110','1101110')
        for word in check_words:
            assert (not Canonical(R.variables,R.constraints,R.alpha,R.beta,word).errors())==witness(J,word)
            counts['canonical_models']+=1
    for J in (I,five,badcycle,irregular):
        for word in words('01',8):
            assert witness(J,word)==border_witness(J,word)
            counts['independent_word_comparisons']+=1
    return dict(status='PASS',seed=2026090656,counts=counts,verdicts=verdicts,
                extra_prefix_profile_checks=extra_repetitions_checked,strict_extension_NO=strict_extension_example,
                context_fixture=context,five_state_NO=five_result,deliberate_cap=cap,
                status_of_proof='Written arguments; not Lean-checked or independently reviewed',
                scope='Target-local marker class, not unrestricted witness existence')


if __name__=='__main__':
    output=check()
    (ROOT/'results/target-tail.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps(output,indent=2))
