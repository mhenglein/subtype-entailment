"""E035: target-frontier normalization, source subsets, and raw decisions.

Finite checks support the implementation. The all-length claims are proved
in the companion note; no cap or failed certificate is a negative verdict.
"""
from collections import deque
from dataclasses import replace
from itertools import product
from pathlib import Path
import hashlib
import json
import random

from border_lab import Instance, words, witness, border_witness
from word_sync import BinaryDFA
from delimited_blocks import BlockSystem, solve_blocks
from marker_certificate import marker_decision
from check_marker_certificate import compile_macro, all_acyclic_paths
from target_frontier import (Limits, Macro, parse_macro, frontier_structure,
                             source_step, complete_observations, _pred,
                             _source_observe, pending_step, target_frontier_decision)

ROOT = Path(__file__).resolve().parents[1]


def logical_run(M, blocks):
    q = M.start
    all_states = []
    runs = []
    for u in blocks:
        local = [q]
        for a in u:
            q = M.delta[q][int(a)]
            if q < 0:
                return None
            local.append(q)
        runs.append(tuple(local))
        all_states.extend(local)
        q = M.delta[q][2]
        if q < 0:
            return None
    all_states.append(q)
    return tuple(runs), tuple(all_states), q


def logical_witness(M, blocks):
    parsed = logical_run(M, blocks)
    if parsed is None or parsed[-1] != M.final:
        return False
    logical = '#'.join(blocks) + '#'
    states = parsed[1]
    assert len(states) == len(logical)+1
    return not any((states[i], states[j]) in M.flags and logical[i:].startswith(logical[j:])
                   for i in range(len(states)) for j in range(i, len(states)))


def observation(word, states, refs, ref_runs, flags):
    eq = 0
    hits = 0
    for j, (v, tr) in enumerate(zip(refs, ref_runs)):
        if word == v:
            eq |= 1 << j
        for t in range(min(len(word), len(v))+1):
            if word[len(word)-t:] == v[len(v)-t:] and (states[len(word)-t], tr[len(v)-t]) in flags:
                hits |= 1 << j
    return eq, hits


def concrete_descriptors(M, schema, refs):
    """Drive the powerset on one fixed reference tuple, not existentially."""
    r = len(refs)
    free = set(M.delta)-set(M.targets)
    pred = _pred(M, free)
    traces = []
    for (begin, end, after), word in zip(schema, refs):
        tr = [begin]
        for a in word:
            tr.append(M.delta[tr[-1]][int(a)])
        assert tr[-1] == end and M.delta[end][2] == after
        traces.append(tr)
    ends = [q for q in free if M.delta[q][2] >= 0
            and (M.delta[q][2] in free or M.delta[q][2] == schema[0][0])]
    coords = tuple(t[-1] for t in traces)
    eq = (1 << r)-1
    S = frozenset((q, q, eq, _source_observe(q, eq, 0, False, coords, M.flags), False) for q in ends)
    for depth in range(max(map(len, refs))+1):
        cols = tuple(u[-1-depth] if depth < len(u) else '_' for u in refs)
        nc = tuple(t[len(u)-depth-1] if depth < len(u) else -1 for t, u in zip(traces, refs))
        S = source_step(S, cols, nc, pred, M.flags)
    return complete_observations(M, S, pred), traces, free, ends


def independent_observations(M, schema, refs, traces, free, ends):
    """Complete bounded oracle: preserve last M+1 symbols then shorten prefix.

    For any longer source block, its earlier target-free path can be shortened
    to at most K-1 edges, preserving the observed suffix and its 'longer' status.
    Thus max_ref_length+K symbols suffice for this fixed-tuple observation test.
    """
    out = set()
    max_length = max(map(len, refs))+len(free)
    for start in sorted(free):
        todo = [('', (start,))]
        while todo:
            u, tr = todo.pop()
            if tr[-1] in ends:
                eq, hit = observation(u, tr, refs, traces, M.flags)
                out.add((start, M.delta[tr[-1]][2], eq, hit, tr[-1]))
            if len(u) < max_length:
                for a, t in enumerate(M.delta[tr[-1]][:2]):
                    if t in free:
                        todo.append((u+str(a), tr+(t,)))
    return out


def main():
    rng = random.Random(2026090654)
    counts = dict(acyclic_instances=0, acyclic_candidates=0, bounded_schemas=0,
                  cyclic_flag_relations=0, independent_schema_calls=0,
                  source_observation_sets=0, direct_word_comparisons=0,
                  normalized_words=0, removed_blocks=0, unsupported_guards=0,
                  intentional_caps=0, uncapped_fixtures=0, canonical_checks=0,
                  three_reference_observation_sets=0, three_reference_words=0, three_reference_decisions=0)
    tallies = {name:{s:0 for s in ('YES','NO','UNKNOWN')} for name in ('acyclic','bounded','cyclic_prefix')}
    # Fixed positive and negative instances, both excluded by the previous marker rule.
    table = ((-1,0,1),(2,1,0),(-1,3,4),(-1,3,4),(-1,5,-1),(-1,5,6),(-1,-1,-1))
    G = frozenset({(2,4),(2,5),(3,4)})
    raw_no = compile_macro(table, 6, G)
    raw_yes = compile_macro(table, 6, G-{(2,4)})
    no = target_frontier_decision(raw_no)
    yes = target_frontier_decision(raw_yes)
    assert marker_decision(raw_no)['status'] == marker_decision(raw_yes)['status'] == 'UNKNOWN'
    assert no['status'] == 'NO' and yes['status'] == 'YES'
    assert yes['result']['prefix_blocks'] == ['', '01']
    assert yes['result']['reference_blocks'] == ('1',)
    assert witness(raw_yes,yes['word']) and border_witness(raw_yes,yes['word'])

    # All 256 relations from four earlier source states into the last target block.
    # Any early marker cycle has two blocks. Deleting two such blocks only
    # removes sources when the only target block is last, so one early marker
    # followed by the exit block suffices. C052 checks the two exact 3-stage
    # schemas, independently of the new powerset solver.
    possible_flags = tuple((p,q) for p in range(4) for q in (4,5))
    for mask in range(1 << len(possible_flags)):
        flags = frozenset(p for h,p in enumerate(possible_flags) if mask >> h & 1)
        raw = compile_macro(table, 6, flags)
        got = target_frontier_decision(raw)
        expected = False
        for second_end in (2,3):
            data = tuple(row[:2] for row in table)
            stages = tuple(BinaryDFA(data, frozenset({end}), start)
                           for start,end in ((0,0),(1,second_end),(4,5)))
            sf = frozenset(((i,p),(j,q)) for i in range(3) for j in range(3) for p,q in flags)
            oracle = solve_blocks(BlockSystem(stages,sf), max_states=None,max_transitions=None)
            counts['independent_schema_calls'] += 1
            assert oracle['status'] != 'UNKNOWN'
            expected |= oracle['status'] == 'YES'
        assert got['status'] != 'UNKNOWN' and (got['status']=='YES') == expected, (mask,got)
        counts['cyclic_flag_relations'] += 1
        tallies['cyclic_prefix'][got['status']] += 1

    # Complete finite raw languages with arbitrary boundary annotations.
    for _ in range(160):
        k = rng.randrange(2,7)
        rows = []
        for q in range(k-1):
            later = [-1]+list(range(q+1,k-1))
            rows.append((rng.choice(later), rng.choice(later), rng.choice([-1]+list(range(q+1,k)))))
        rows.append((-1,-1,-1))
        flags = frozenset((p,q) for p in range(k) for q in range(k) if rng.random()<.08)
        bad = frozenset(q for q in range(k) if rng.random()<.03)
        raw = compile_macro(tuple(rows),k-1,flags,bad)
        good = False
        for word in all_acyclic_paths(raw):
            x = witness(raw,word)
            assert x == border_witness(raw,word)
            good |= x
            counts['acyclic_candidates'] += 1
        got = target_frontier_decision(raw)
        assert got['status'] != 'UNKNOWN' and (got['status']=='YES') == good, (raw,got)
        counts['acyclic_instances'] += 1
        tallies['acyclic'][got['status']] += 1

    # Arbitrary nonflat stage DFAs already covered by the exact prior C052 solver.
    for _ in range(160):
        r = rng.randrange(1,4)
        ms = []
        for j in range(r):
            k = rng.randrange(1,3)
            ms.append(BinaryDFA(tuple(tuple(rng.randrange(-1,k) for a in range(2)) for q in range(k)),
                                frozenset(q for q in range(k) if rng.random()<.7),rng.randrange(k)))
        nodes = [(i,q) for i,m in enumerate(ms) for q in range(len(m.delta))]+[(r,0)]
        flags = frozenset((p,q) for p in nodes for q in nodes if rng.random()<.06)
        bad = frozenset(p for p in nodes if rng.random()<.02)
        S = BlockSystem(tuple(ms),flags,bad)
        raw,_ = S.compile()
        expected = solve_blocks(S,max_states=None,max_transitions=None)
        got = target_frontier_decision(raw)
        assert got['status'] == expected['status'] and got['status'] != 'UNKNOWN', (S,got,expected)
        counts['bounded_schemas'] += 1
        tallies['bounded'][got['status']] += 1

    # Two reference blocks force persistent pending context checks, not just
    # independent comparison with the final block. Prefix markers can cycle.
    two = ((-1,0,1),(2,1,0),(-1,2,3),(3,3,4),(-1,-1,-1))
    possible = tuple((p,q) for p in (0,1) for q in (2,3))
    normalization_example = None
    for trial in range(120):
        flags = frozenset(p for p in possible if rng.random()<.4)
        if not any(q==2 for _,q in flags):
            flags |= frozenset({(0,2)})
        M = Macro(dict(enumerate(two)),0,4,flags)
        left = '0'+'1'*rng.randrange(4)
        right = rng.choice(('', '0','1','01','001','011'))
        refs = (left,right)
        schema = ((1,2,3),(3,3,4))
        observed, traces, free, ends = concrete_descriptors(M,schema,refs)
        expected = independent_observations(M,schema,refs,traces,free,ends)
        assert observed == expected, (flags,refs,observed^expected)
        counts['source_observation_sets'] += 1
        raw = compile_macro(two,4,flags)
        for repetition in (1,3,5,11,13):
            prefix = tuple('1'*rng.randrange(4) for _ in range(repetition))
            blocks = prefix+refs
            x = logical_witness(M,blocks)
            w = M.expand(blocks)
            assert x == witness(raw,w) == border_witness(raw,w)
            counts['direct_word_comparisons'] += 1
            if not x:
                continue
            # Repeated (boundary state,pending) deletion, with fixed reference.
            current = list(prefix)
            original_length = len(current)
            while True:
                run = logical_run(M,tuple(current)+refs)
                prefix_runs = run[0][:len(current)]
                q = M.start
                pending = 0
                visited = {(q,pending):0}
                removed = False
                for i,(u,tr) in enumerate(zip(current,prefix_runs)):
                    eq,hits = observation(u,tr,refs,traces,flags)
                    pending = pending_step(pending,eq,hits,len(refs))
                    assert pending is not None
                    q = M.delta[tr[-1]][2]
                    key = (q,pending)
                    if key in visited:
                        a,b = visited[key],i+1
                        del current[a:b]
                        assert logical_witness(M,tuple(current)+refs)
                        removed = True
                        break
                    visited[key] = i+1
                if not removed:
                    break
            assert len(current) <= len(two)*(1 << (len(refs)-1))-1
            new = tuple(current)+refs
            assert witness(raw,M.expand(new)) and border_witness(raw,M.expand(new))
            counts['normalized_words'] += 1
            counts['removed_blocks'] += original_length-len(current)
            if normalization_example is None and original_length >= 11:
                normalization_example = dict(flags=sorted(flags),before=blocks,after=new,
                                             before_prefix_blocks=original_length,after_prefix_blocks=len(current),
                                             reference=refs)

    # Three reference blocks exercise two distinct pending-pattern positions.
    # A separate RNG keeps earlier fixtures and canonical paths reproducible.
    rng3 = random.Random(2026090655)
    three = ((-1,0,1),(2,1,0),(-1,2,3),(3,3,4),(4,4,5),(-1,-1,-1))
    for trial in range(20):
        flags = frozenset((p,q) for p in (0,1) for q in (2,3) if rng3.random()<.5)
        flags |= frozenset({(0,2)})
        M = Macro(dict(enumerate(three)),0,5,flags)
        refs = ('0'+'1'*rng3.randrange(3), rng3.choice(('','1','11','01')),
                rng3.choice(('','1','11','01')))
        schema = ((1,2,3),(3,3,4),(4,4,5))
        observed, traces, free, ends = concrete_descriptors(M,schema,refs)
        assert observed == independent_observations(M,schema,refs,traces,free,ends)
        counts['three_reference_observation_sets'] += 1
        raw = compile_macro(three,5,flags)
        ref_only = Macro(M.delta,1,5,flags)
        for h in (1,3,5,7,9):
            prefix = tuple('1'*rng3.randrange(3) for _ in range(h))
            blocks = prefix+refs
            runs = logical_run(M,blocks)[0]
            mask = 0
            for u,tr in zip(prefix,runs[:h]):
                eq,hits = observation(u,tr,refs,traces,flags)
                mask = pending_step(mask,eq,hits,3)
                if mask is None:
                    break
            if mask is not None:
                for u in refs:
                    eq = sum(1<<j for j,v in enumerate(refs) if u==v)
                    mask = pending_step(mask,eq,0,3)
                    if mask is None:
                        break
            predicted = mask is not None and logical_witness(ref_only,refs)
            word = M.expand(blocks)
            assert predicted == logical_witness(M,blocks) == witness(raw,word) == border_witness(raw,word)
            counts['three_reference_words'] += 1

    for flags in (frozenset({(0,2)}),frozenset({(0,2),(1,2),(0,3),(1,3)})):
        got = target_frontier_decision(compile_macro(three,5,flags))
        assert got['status']=='YES' and len(got['result']['reference_blocks'])==3
        counts['three_reference_decisions'] += 1

    # Scope and cap guards. No valid claimed answer is manufactured on failure.
    bad_cycle = compile_macro(table,6,frozenset({(3,0)}))
    unknown = target_frontier_decision(bad_cycle)
    assert unknown['status'] == 'UNKNOWN'
    counts['unsupported_guards'] += 1
    odd = compile_macro(table,6,G)
    odd = replace(odd,flags=frozenset({(15,2)}))
    assert target_frontier_decision(odd)['status'] == 'UNKNOWN'
    counts['unsupported_guards'] += 1
    irregular=Instance(((1,-1),(-1,2),(-1,-1)),frozenset({2}))
    assert target_frontier_decision(irregular)['status']=='UNKNOWN'
    counts['unsupported_guards'] += 1
    assert target_frontier_decision(Instance(((0,0),),frozenset({0})))['status']=='UNKNOWN'
    counts['unsupported_guards'] += 1
    assert target_frontier_decision(Instance(((-1,-1),),frozenset({0})))['word']==''
    cap_results = {}
    for key in ('states','transitions','descriptors','reconstruction'):
        cap = target_frontier_decision(raw_yes, replace(Limits(),**{key:1}))
        assert cap['status']=='UNKNOWN', (key,cap)
        cap_results[key] = cap.get('reason')
        counts['intentional_caps'] += 1

    two_raw = compile_macro(two,4,frozenset({(0,2)}))
    schema_cap = target_frontier_decision(two_raw,replace(Limits(),schemas=1))
    assert schema_cap['status']=='UNKNOWN'
    cap_results['schemas'] = schema_cap.get('reason')
    counts['intentional_caps'] += 1
    for raw, wanted in ((raw_no,'NO'),(raw_yes,'YES')):
        unlimited = target_frontier_decision(raw,Limits(None,None,None,None,None))
        assert unlimited['status'] == wanted
        counts['uncapped_fixtures'] += 1

    # Exact regular-model checks for the positive/negative cyclic-prefix pair.
    from terminal_realization import realize
    from denial_bridge import Canonical
    for raw in (raw_yes,raw_no):
        R = realize(raw)
        for w in (yes['word'],'0010001100','001011001100','001111001011001100'):
            assert (not Canonical(R.variables,R.constraints,R.alpha,R.beta,w).errors()) == witness(raw,w)
            counts['canonical_checks'] += 1

    def blob(n):
        data=(ROOT/'experiments'/n).read_bytes()
        return hashlib.sha1(('blob %d\0'%len(data)).encode()+data).hexdigest()
    return dict(status='PASS',seed=2026090654,counts=counts,verdicts=tallies,
                cyclic_prefix_NO=no,cyclic_prefix_YES=yes,normalization_example=normalization_example,
                unsupported_marker_cycle=unknown,cap_results=cap_results,
                dependency_blobs={n:blob(n) for n in ('border_lab.py','delimited_blocks.py','marker_certificate.py')},
                proof_status='Written proofs; not independently reviewed or Lean-checked',
                scope='Early marker cycles allowed; no marker cycle reachable from any relevant flag target')


if __name__=='__main__':
    result=main()
    out=ROOT/'results'/'target-frontier.json'
    out.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
