"""Independent finite regressions for the source-capture reduction.

No bounded enumeration is used as a general decision procedure. The optional
SMT probes test the generated formula, not a claim of complete Z3 solving.
"""
import argparse
from dataclasses import replace
from itertools import product
from pathlib import Path
import json
import random
import re
import subprocess
import sys

from border_lab import Instance, words, witness, border_witness
from source_capture import (capture_prefix, capture_clause, capture_language,
    no_capture_language, path_dfa, single_source_normal_form, compile_single_source,
    compile_source_sequence, between_sources, after_last_source, validate_terminal)

SEED = 2026090917


def direct_root(I, p, t, w):
    """Use the actual run cut and a direct factor comparison, not capture."""
    c = replace(I, start=p).run(w)
    return not any(c[j] == t and w[:len(w)-j] == w[j:]
                   for j in range(len(w) + 1))


def root_checks():
    counts = dict(tables=0, accepted_cases=0, target_checks=0,
                  nonempty_captures=0, empty_captures=0, absent_captures=0,
                  nonsuffix_cases=0, wrong_state_cases=0)
    ws = tuple(words('01', 6))
    for entries in product(range(-1, 3), repeat=4):
        table = (entries[:2], entries[2:], (-1, -1))
        counts['tables'] += 1
        for mask in range(8):
            bad = frozenset(q for q in range(3) if mask >> q & 1)
            for p in range(3):
                I = Instance(table, frozenset({2}), bad=bad, start=p)
                captures = [capture_language(I, t) for t in range(3)]
                absences = [no_capture_language(I, t) for t in range(3)]
                for w in ws:
                    if not I.admissible(w):
                        continue
                    counts['accepted_cases'] += 1
                    for t in range(3):
                        vs = [w[:j] for j in range(len(w)+1)
                              if captures[t].accepts(w[:j])]
                        assert len(vs) <= 1, (I, t, w, vs)
                        v = capture_prefix(I, t, w)
                        assert v == (vs[0] if vs else None)
                        assert absences[t].accepts(w) == (v is None)
                        assert capture_clause(I, p, t, w) == direct_root(I, p, t, w)
                        counts['target_checks'] += 1
                        if v is None:
                            counts['absent_captures'] += 1
                        elif v == '':
                            counts['empty_captures'] += 1
                        else:
                            counts['nonempty_captures'] += 1
                            if not w.endswith(v):
                                counts['nonsuffix_cases'] += 1
                            elif capture_clause(I, p, t, w):
                                counts['wrong_state_cases'] += 1
    return counts



def long_path_checks():
    rng = random.Random(SEED+3)
    counts = dict(instances=0, accepted_paths=0, target_checks=0,
                  longest_word=0, overlapping_violations=0)
    for _ in range(300):
        k = rng.randrange(3,10)
        # A guaranteed route to terminal, with independent recurrent 1-edges.
        table = tuple((q+1,rng.randrange(k-1)) if q<k-1 else (-1,-1)
                      for q in range(k))
        p = rng.randrange(k-1)
        I = Instance(table,frozenset({k-1}),start=p)
        counts['instances'] += 1
        for repeat in range(6):
            w = ''; q = p
            for length in range(80):
                # Include paths that stay recurrent for a while, then finish.
                a = int(rng.random() < 0.72)
                w += str(a); q = table[q][a]
                if q == k-1:
                    break
            while q != k-1:
                w += '0'; q = table[q][0]
            assert I.admissible(w)
            counts['accepted_paths'] += 1
            counts['longest_word'] = max(counts['longest_word'],len(w))
            for t in range(k):
                assert capture_clause(I,p,t,w) == direct_root(I,p,t,w)
                counts['target_checks'] += 1
            c=I.run(w)
            counts['overlapping_violations'] += sum(
                w[j:] == w[:len(w)-j] and j < len(w)-j
                for j in range(1,len(w)))
    return counts


def normalization_checks():
    rng = random.Random(SEED)
    counts = dict(instances=0, word_checks=0, witnesses=0, shortened=0,
                  sequences_checked=0)
    ws = tuple(words('01', 8))
    for _ in range(240):
        k = rng.randrange(2, 7)
        finals = frozenset({k-1} | ({k-2} if rng.randrange(4) == 0 else set()))
        table = tuple((-1, -1) if q in finals else
                      tuple(rng.randrange(-1, k) for _ in range(2)) for q in range(k))
        p = rng.randrange(k)
        flags = frozenset((p, t) for t in range(k) if rng.randrange(2))
        bad = frozenset(q for q in range(k) if rng.randrange(7) == 0)
        I = Instance(table, finals, flags, bad, rng.randrange(k))
        validate_terminal(I)
        counts['instances'] += 1
        S = {a for a, _ in flags}
        for w in ws:
            counts['word_checks'] += 1
            expected = witness(I, w)
            assert expected == border_witness(I, w)
            if not I.admissible(w):
                continue
            c = I.run(w)
            actual = all(capture_clause(I, c[i], t, w[i:])
                         for i in range(len(w)+1) for s, t in flags if c[i] == s)
            assert actual == expected
            counts['sequences_checked'] += 1
            if expected:
                counts['witnesses'] += 1
                v = single_source_normal_form(I, w)
                assert witness(I, v) and border_witness(I, v)
                assert sum(q in S for q in I.run(v)) <= 1
                counts['shortened'] += (len(v) < len(w))
    return counts


def source_segment_checks():
    rng = random.Random(SEED+1)
    counts = dict(instances=0, accepted_words=0, reconstructed=0)
    ws = tuple(words('01', 7))
    for _ in range(200):
        k = rng.randrange(2, 7)
        finals = frozenset({k-1} | ({k-2} if rng.randrange(5) == 0 else set()))
        table = tuple((-1, -1) if q in finals else
                      tuple(rng.randrange(-1, k) for _ in range(2)) for q in range(k))
        flags = frozenset((p,t) for p in range(k) for t in range(k) if rng.randrange(5) == 0)
        I = Instance(table, finals, flags, start=rng.randrange(k))
        S = {p for p, _ in flags}
        counts['instances'] += 1
        for w in ws:
            if not I.admissible(w):
                continue
            counts['accepted_words'] += 1
            c = I.run(w)
            cuts = [i for i,q in enumerate(c) if q in S]
            if not cuts:
                assert path_dfa(I, I.start, I.final, forbidden=S).accepts(w)
                continue
            sequence = [c[i] for i in cuts]
            assert path_dfa(I, I.start, {sequence[0]},
                           forbidden=S-{sequence[0]}, stop=sequence[0]).accepts(w[:cuts[0]])
            for a,b in zip(cuts,cuts[1:]):
                assert between_sources(I,c[a],c[b],S).accepts(w[a:b])
            assert after_last_source(I,c[cuts[-1]],S).accepts(w[cuts[-1]:])
            captured = all(capture_clause(I,c[i],t,w[i:]) for i in cuts
                           for s,t in flags if c[i] == s)
            assert captured == witness(I,w) == border_witness(I,w)
            counts['reconstructed'] += 1
    return counts


def guards_and_counterexamples():
    # Terminality is essential: first accepted prefix can be harmless while a
    # later accepted prefix is the actual suffix in a forbidden comparison.
    nonterminal = Instance(((1,1),(1,2),(-1,-1)), frozenset({1,2}), frozenset({(0,1)}))
    failures = []
    for w in words('01', 7):
        if nonterminal.admissible(w) and capture_clause(nonterminal,0,1,w) != direct_root(nonterminal,0,1,w):
            failures.append(w)
            break
    assert failures, 'Need explicit nonterminal regression'
    for compiler in (compile_single_source,):
        try:
            compiler(nonterminal)
        except ValueError:
            pass
        else:
            raise AssertionError('Nonterminal instance accepted')
    # Nonvacuous second source: (2,0) also forbids an actual comparison on
    # 101010. Splicing source 2 preserves acceptance but creates (0,1).
    multi = Instance(((1,2),(4,1),(3,2),(1,0),(-1,-1)),
                     frozenset({4}),frozenset({(0,1),(2,0)}))
    old, new = '110010', '10010'
    assert witness(multi, old) and border_witness(multi, old)
    assert multi.admissible(new) and not witness(multi, new)
    assert multi.run(new)[0] == 0 and multi.run(new)[3] == 1
    assert new.startswith(new[3:])
    assert multi.run(old)[1] == multi.run(old)[2] == 2
    oneflag = replace(multi, flags=frozenset({(2,0)}))
    assert oneflag.admissible('101010') and not witness(oneflag,'101010')
    try:
        compile_single_source(multi)
    except ValueError:
        pass
    else:
        raise AssertionError('Multi-source instance accepted by single-source compiler')
    return {'multi_source_loop_failure': {
        'delta':multi.delta,'final':sorted(multi.final),'flags':sorted(multi.flags),
        'word':old,'shortened':new,'deleted_interval':[1,2],'repeated_source':2,
        'new_violation_cuts':[0,3], 'second_flag_violation_example':'101010'},
        'nonterminal_first_capture_failure': {
        'delta': nonterminal.delta, 'final': sorted(nonterminal.final),
        'flags': sorted(nonterminal.flags), 'word': failures[0],
        'capture_clause': capture_clause(nonterminal,0,1,failures[0]),
        'direct_root': direct_root(nonterminal,0,1,failures[0])}}


def smt_probe(I, expected, name, fixed=None, sequence=None, timeout=8):
    P = compile_single_source(I) if sequence is None else compile_source_sequence(I,sequence)
    script = P.smt2(fixed_word=fixed, timeout_ms=int((timeout-1)*1000))
    runner = Path(__file__).with_name('_word_smt_native.py')
    try:
        proc = subprocess.run([sys.executable,str(runner),'W'], input=script,
                              text=True,capture_output=True,timeout=timeout)
    except subprocess.TimeoutExpired:
        return {'name':name,'status':'UNKNOWN','reason':'wall-time cap'}
    lines = proc.stdout.strip().splitlines()
    first = lines[0].strip() if lines else 'unknown'
    if first == 'sat':
        match = re.search(r'\(\(W "([01]*)"\)\)',proc.stdout)
        if match is None:
            raise AssertionError(('Missing binary model',proc.stdout,proc.stderr))
        w = match[1]
        assert witness(I,w) and border_witness(I,w), (name,w)
        assert expected is not False, (name,'unexpected SAT',w)
        return {'name':name,'status':'SAT','word':w,'independent_witness_check':True,
                'formula_variables':len(P.variables),'regular_atoms':len(P.languages)}
    if first == 'unsat':
        assert expected is not True, (name,'unexpected UNSAT')
        return {'name':name,'status':'UNSAT','trust':'optional SMT backend, not a proof certificate',
                'formula_variables':len(P.variables),'regular_atoms':len(P.languages)}
    if first == 'unknown':
        return {'name':name,'status':'UNKNOWN','reason':'backend unknown or unavailable'}
    if proc.returncode or '(error ' in proc.stdout:
        raise AssertionError((name,proc.returncode,proc.stdout,proc.stderr))
    return {'name':name,'status':'UNKNOWN','reason':'backend returned unknown'}


def smt_checks():
    five = Instance((( -1,1),(-1,2),(-1,3),(2,4),(-1,-1)),frozenset({4}),frozenset({(0,1)}))
    six = Instance(((1,-1),(4,-1),(5,4),(2,1),(3,-1),(-1,-1)),frozenset({5}),frozenset({(0,1)}))
    cases = [
        (Instance(((-1,-1),),frozenset({0})),True,'empty_word'),
        (Instance(((-1,-1),),frozenset({0}),frozenset({(0,0)})),False,'diagonal_empty_NO'),
        (Instance(((1,-1),(-1,-1)),frozenset({1}),frozenset({(0,1)})),False,'empty_suffix_NO'),
        (five,True,'five_state_extremal'),
        (six,True,'six_state_extremal'),
        (Instance(((1,2),(1,2),(-1,-1)),frozenset({2}),frozenset({(1,1)})),True,'avoid_diagonal_source'),
        (Instance(((1,-1),(1,2),(-1,-1)),frozenset({2}),frozenset({(1,0)})),True,'interior_recurrent_source'),
        (Instance(((1,-1),(1,2),(-1,-1)),frozenset({2}),frozenset({(1,2)})),False,'interior_empty_suffix_NO'),
        (Instance(((1,2),(-1,-1),(-1,-1)),frozenset({1,2}),frozenset({(0,1)})),True,'multiple_finals'),
        (Instance(((1,2),(-1,-1),(-1,-1)),frozenset({1,2}),frozenset({(0,1)}),frozenset({2})),False,'Bad_removes_only_witness')
    ]
    results = [smt_probe(I,expected,name) for I,expected,name in cases]
    results += [smt_probe(five,True,'five_fixed_witness','111011'),
                smt_probe(five,False,'five_fixed_nonwitness','1111')]
    multi = Instance(((1,2),(4,1),(3,2),(1,0),(-1,-1)),
                     frozenset({4}),frozenset({(0,1),(2,0)}))
    results += [smt_probe(multi,True,'multi_sequence_recurrence','110010',sequence=(0,2,2)),
                smt_probe(multi,False,'multi_sequence_new_violation','10010',sequence=(0,2)),
                smt_probe(multi,False,'multi_sequence_wrong_count','110010',sequence=(0,2))]
    rng = random.Random(SEED+2)
    # Pin 36 actual accepted words, not just arbitrary usually-rejected strings.
    # The finite enumeration selects probes, never certifies nonexistence.
    probes = 0
    for attempt in range(1000):
        k = rng.randrange(2,5)
        table = tuple(tuple(rng.randrange(-1,k) for _ in range(2)) if q<k-1
                      else (-1,-1) for q in range(k))
        flags = frozenset((p,t) for p in range(k) for t in range(k) if rng.randrange(5)==0)
        I = Instance(table,frozenset({k-1}),flags,start=rng.randrange(k))
        candidates = [w for w in words('01',6) if I.admissible(w)]
        if not candidates:
            continue
        w = rng.choice(candidates)
        S = {p for p,_ in flags}
        seq = tuple(q for q in I.run(w) if q in S)
        results.append(smt_probe(I,witness(I,w),'fixed_sequence_'+str(probes),w,sequence=seq))
        probes += 1
        if probes == 36:
            break
    assert probes == 36
    return results


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--with-smt', action='store_true')
    args = parser.parse_args()
    result = {'seed':SEED, 'root_capture':root_checks(), 'long_recurrent_paths':long_path_checks(),
              'single_source_normalization':normalization_checks(),
              'source_segments':source_segment_checks(),
              'guards':guards_and_counterexamples(),
              'evidence':'finite regressions; all-length theorem is the linked written argument'}
    if args.with_smt:
        result['optional_smt'] = smt_checks()
        result['optional_backend_note'] = 'Local run: native Z3 4.13.3.0; model words may vary; SAT independently checked; UNSAT backend-trusted.'
    name = 'source-capture-smt.json' if args.with_smt else 'source-capture.json'
    path = Path(__file__).resolve().parents[1]/'results'/name
    path.parent.mkdir(exist_ok=True)
    path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps(result,indent=2,sort_keys=True))

if __name__ == '__main__':
    main()
