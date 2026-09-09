"""Independent finite regression for exact terminal one-flag counting.

All-length completeness is in the proof note; enumeration is implementation
checking. Direct literal periods and two existing witness definitions are the
oracles. No bounded failure is used as an unrestricted negative except under
the separately recorded complete <=3-state or <=4-state terminal theorems.
"""
import hashlib
import itertools
import json
import random
from collections import Counter
from pathlib import Path
from border_lab import Instance, witness, border_witness, words
from one_flag_counting import MonoidCounter, solve_one_flag, solve_one_source_unambiguous

ROOT = Path(__file__).resolve().parents[1]


def direct_periods(I, word, targets):
    c = I.run(word)
    if not I.admissible(word):
        return ()
    return tuple(d for d in range(1, len(word))
                 if c[d] in targets and word[d:] == word[:len(word)-d])


def representations(word):
    out = []
    N = len(word)
    for d in range(1, N):
        e, r = divmod(N, d)
        u, v = word[:r], word[r:d]
        if (u+v)*e+u == word:
            out.append((d, e, u, v))
    return out


def accepted_words_dag(I):
    assert all(t < 0 or t > q for q, row in enumerate(I.delta) for t in row)
    todo = [('', I.start)]
    out = []
    while todo:
        w, q = todo.pop()
        if q in I.final:
            out.append(w)
        for a, t in enumerate(I.delta[q]):
            if t >= 0:
                todo.append((w+str(a), t))
    return out


def poly_mul(a, b):
    out = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += x*y
    return trim(out)


def trim(a):
    while len(a)>1 and a[-1] == 0:
        a.pop()
    return a


def determinant_denominator(C):
    """Independent Newton identities for det(I-zA); integer arithmetic only."""
    n = C.m
    M = [[0]*n for _ in range(n)]
    for i, row in enumerate(C.next):
        for j in row:
            M[i][j] += 1
    power = [[int(i == j) for j in range(n)] for i in range(n)]
    traces = [0]
    d = [1]
    for j in range(1, n+1):
        power = [[sum(power[i][h]*M[h][t] for h in range(n)) for t in range(n)]
                 for i in range(n)]
        traces.append(sum(power[i][i] for i in range(n)))
        numerator = -sum(d[j-h]*traces[h] for h in range(1, j+1))
        assert numerator % j == 0
        d.append(numerator//j)
    return trim(d)


def complete_count_oracle(I, targets, max_len, stats):
    C = MonoidCounter(I, frozenset(targets), max_monoid=None, max_work=None)
    accepts, hits, good = Counter(), Counter(), Counter()
    for w in words('01', max_len):
        stats['raw_word_checks'] += 1
        if not I.admissible(w):
            continue
        n = len(w)
        pds = direct_periods(I, w, targets)
        reps = representations(w)
        c = I.run(w)
        selected = [r for r in reps if c[r[0]] in targets]
        assert [r[0] for r in selected] == list(pds)
        assert all(1 <= e <= C.k-1 and v for d, e, u, v in selected)
        assert len(pds) == len(set(c[d] for d in pds))
        accepts[n] += 1
        hits[n] += len(pds)
        good[n] += int(not pds)
        stats['accepted_word_checks'] += 1
        stats['period_incidences'] += len(pds)
        if len(targets) <= 1:
            assert len(pds) <= 1
            assert (not pds) == witness(I, w) == border_witness(I, w)
    for n in range(max_len+1):
        A, H, difference = C.counts(n)
        assert A == accepts[n] and H == hits[n], (I, targets, n, (A,H), (accepts[n],hits[n]))
        if len(targets) <= 1:
            assert difference == good[n]
        stats['exact_length_coefficients'] += 1
    return C


def check():
    rng = random.Random(2026090917)
    stats = dict(raw_word_checks=0, accepted_word_checks=0, period_incidences=0,
                 exact_length_coefficients=0, full_three_state_queries=0,
                 sampled_four_state_queries=0, finite_dag_queries=0,
                 finite_dag_words=0, normalized_random_tables=0,
                 symbolic_denominator_checks=0, scope_guards=0, caps=0)
    # All 256 binary terminal 3-state tables, all nine singleton flag relations.
    # The pre-existing <=3-state theorem gives a complete length-six oracle.
    verdicts = Counter()
    for entries in itertools.product(range(-1, 3), repeat=4):
        table = (entries[:2], entries[2:], (-1, -1))
        for p, q in itertools.product(range(3), repeat=2):
            I = Instance(table, frozenset({2}), frozenset({(p,q)}))
            expected = any(witness(I, w) for w in words('01', 6))
            answer = solve_one_flag(I, max_monoid=None, max_work=None,
                                    max_coefficients=None, max_reconstruction=None)
            assert answer['status'] in ('YES', 'NO') and (answer['status']=='YES') == expected, (I,answer)
            stats['full_three_state_queries'] += 1
            verdicts[answer['status']] += 1
    # Sample arbitrary 4-state singleton flags; prior terminal census is complete through length four.
    for _ in range(320):
        table = tuple(tuple(rng.randrange(-1,4) for _ in range(2)) for q in range(3)) + ((-1,-1),)
        I = Instance(table, frozenset({3}), frozenset({(rng.randrange(4),rng.randrange(4))}),
                     frozenset(q for q in range(4) if rng.random()<.07), rng.randrange(4))
        expected = any(witness(I,w) for w in words('01',4))
        result=solve_one_flag(I,max_monoid=None,max_work=None,max_coefficients=None,max_reconstruction=None)
        assert result['status'] in ('YES','NO') and (result['status']=='YES')==expected,(I,result)
        stats['sampled_four_state_queries']+=1
    # Every no-return 3-state table: independently compare the series, not just the decision.
    for entries in itertools.product((-1,1,2), repeat=4):
        I=Instance((entries[:2],entries[2:],(-1,-1)),frozenset({2}),frozenset({(0,1)}))
        complete_count_oracle(I,{1},8,stats)
    # Longer cyclic count comparisons; no short-word negative conclusions here.
    for _ in range(120):
        k=rng.randrange(3,7)
        table=tuple(tuple(rng.choice([-1]+list(range(1,k))) for _ in range(2)) for q in range(k-1))+((-1,-1),)
        t=rng.randrange(1,k-1)
        I=Instance(table,frozenset({k-1}),frozenset({(0,t)}))
        complete_count_oracle(I,{t},8,stats)
        stats['normalized_random_tables']+=1
    # Acyclic complete candidate languages, arbitrary initial source, multiple finals, and Bad.
    dag_verdicts=Counter()
    for _ in range(300):
        k=rng.randrange(1,9)
        finals=frozenset(q for q in range(k) if q==k-1 or rng.random()<.2)
        table=tuple((-1,-1) if q in finals else tuple(rng.choice([-1]+list(range(q+1,k))) for _ in range(2))
                    for q in range(k))
        p,q=rng.randrange(k),rng.randrange(k)
        I=Instance(table,finals,frozenset({(p,q)}),frozenset(q for q in range(k) if rng.random()<.1),rng.randrange(k))
        candidates=accepted_words_dag(I)
        expected=any(witness(I,w) for w in candidates)
        out=solve_one_flag(I,max_monoid=None,max_work=None,max_coefficients=None,max_reconstruction=None)
        assert (out['status']=='YES')==expected and out['status']!='UNKNOWN'
        stats['finite_dag_queries']+=1;stats['finite_dag_words']+=len(candidates)
        dag_verdicts[out['status']]+=1
    negative=Instance(((-1,1),(1,2),(-1,-1)),frozenset({2}),frozenset({(0,1)}))
    positive=Instance(((-1,1),(-1,2),(-1,3),(2,4),(-1,-1)),frozenset({4}),frozenset({(0,1)}))
    # The six-state extremal single-source example recorded by the other agent.
    unequal=Instance(((-1,1),(2,1),(-1,3),(4,3),(-1,-1)),frozenset({4}),frozenset({(0,2)}))
    six=Instance(((1,-1),(4,-1),(5,4),(2,1),(3,-1),(-1,-1)),frozenset({5}),frozenset({(0,1)}))
    fixture_results=[]
    for name,I in (('infinite_no_10star1',negative),('infinite_yes_11101star1',positive),('six_state_extremal',six),('nonregular_unequal_blocks',unequal)):
        ans=solve_one_flag(I,max_monoid=None,max_work=None,max_coefficients=None,max_reconstruction=None)
        fixture_results.append(dict(name=name,result=ans))
    assert fixture_results[0]['result']['status']=='NO'
    assert fixture_results[1]['result']['word']=='111011'
    assert fixture_results[2]['result']['word']=='00001000'
    U=complete_count_oracle(unequal,{2},12,stats)
    for n in range(50):
        assert U.counts(n)==(max(0,n-3),int(n>=4 and n%2==0),max(0,n-3)-int(n>=4 and n%2==0))
    for name,I in (('negative',negative),('positive',positive)):
        C=MonoidCounter(I,frozenset({1}),None,None)
        d=determinant_denominator(C)
        Q=[1]
        for j in range(1,C.k+1):
            dj=[0]*(j*(len(d)-1)+1)
            for i,c in enumerate(d):dj[j*i]=c
            Q=poly_mul(Q,dj)
        counts=[C.counts(n)[2] for n in range(C.bound+12)]
        coeff=[sum(Q[i]*counts[n-i] for i in range(min(n,len(Q)-1)+1)) for n in range(len(counts))]
        assert all(x==0 for x in coeff[C.bound:])
        if name=='negative': assert not any(counts)
        else: assert all(counts[n]==int(n>=6 and n%2==0) for n in range(len(counts)))
        stats['symbolic_denominator_checks']+=len(coeff)
    # First-moment subtraction can vanish IDENTICALLY despite a good word.
    cancellation=Instance(((1,-1),(2,4),(3,-1),(6,-1),(-1,5),(6,-1),(-1,-1)),
                          frozenset({6}),frozenset({(0,1),(0,2)}))
    C=complete_count_oracle(cancellation,{1,2},8,stats)
    assert C.counts(4)==(2,2,0) and witness(cancellation,'0110')
    assert not witness(cancellation,'0000')
    assert solve_one_source_unambiguous(cancellation)['status']=='UNKNOWN'
    stats['scope_guards']+=1
    # Antichain targets give a checkable multi-target extension, with infinitely many candidates.
    antichain=Instance(((1,2),(3,1),(2,3),(-1,-1)),frozenset({3}),frozenset({(0,1),(0,2)}))
    ant=solve_one_source_unambiguous(antichain,max_monoid=None,max_work=None,max_coefficients=None,max_reconstruction=None)
    assert ant['status']=='NO' # candidates 0 1* 0 and 1 0* 1, each with a flagged one-letter border.
    for cap in ({'max_monoid':1},{'max_work':1},{'max_coefficients':1}):
        assert solve_one_flag(negative,**cap)['status']=='UNKNOWN'
        stats['caps']+=1
    assert solve_one_flag(positive,max_reconstruction=1)['status']=='UNKNOWN';stats['caps']+=1
    try:
        solve_one_flag(Instance(((0,0),),frozenset({0})))
        raise AssertionError('Nonterminal finals were accepted')
    except ValueError:stats['scope_guards']+=1
    assert solve_one_flag(cancellation)['status']=='UNKNOWN';stats['scope_guards']+=1
    for I in (Instance(((-1,-1),),frozenset({0})),Instance(((-1,-1),),frozenset({0}),frozenset({(0,0)}))):
        ans=solve_one_flag(I)
        assert (ans['status']=='YES')==witness(I,'');stats['scope_guards']+=1
    raw=(ROOT/'experiments/border_lab.py').read_bytes()
    blob=hashlib.sha1(('blob %d\0'%len(raw)).encode()+raw).hexdigest()
    return dict(status='PASS',seed=2026090917,base='05b20ee73841d0e7105a44beb761e553a7081a8d',
                counts=stats,three_state_verdicts=dict(verdicts),dag_verdicts=dict(dag_verdicts),
                fixtures=fixture_results,cancellation=dict(delta=cancellation.delta,flags=sorted(cancellation.flags),
                         words=['0000','0110'],accepted_count=2,period_incidence_count=2,witness_count=1),
                antichain_result=ant,border_lab_blob=blob,
                proof_status='Written rational-series proof; not independently reviewed or Lean-checked',
                scope='Every terminal one-flag instance; certified mutually-unreachable target sets; not arbitrary multi-flag existence')


if __name__=='__main__':
    out=check()
    (ROOT/'results/one-flag-counting.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
