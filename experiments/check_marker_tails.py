"""Independent finite oracles and regressions for semantic marker-tail search.

All-length claims are in the proof note. No finite census is a completeness
proof for unrestricted Problem 1.7. This script writes a deterministic result.
"""
from collections import deque
from itertools import product
import json
from pathlib import Path
import random

from border_lab import Instance, Sandwich, words, witness, border_witness, necessary
from marker_tail import (Limits, normalized_slice, relaxed_decision, solve_slice,
                         tail_safe, reach)
from marker_spectrum import (weighted_fibres, cost_lasso, last_aligned, realize,
                             semantic_decision, spectrum_slice)

SEED = 2026090821
UNCAPPED = Limits(**{name:None for name in Limits.__dataclass_fields__})


def independent_tail(I,w,H):
    """Reversal/border specification, not the forward-cut implementation."""
    if not I.admissible(w):
        return False
    rev,c = w[::-1],I.run(w)[::-1]
    for length in range(len(rev)+1):
        for border in range(length+1):
            if (c[length],c[border]) not in I.flags:
                continue
            boundary = border == 0 or border == length
            if (boundary or (w and rev[:border].count(w[-1]) <= H)):
                if rev[:border] == rev[length-border:length]:
                    return False
    return True


def all_last_costs(I,w,letters):
    """Enumerate marked comparisons directly in reversed prefix coordinates."""
    if not I.admissible(w):
        return []
    rev,c = w[::-1],I.run(w)[::-1]
    if any((q,q) in I.flags or (q,c[0]) in I.flags for q in c):
        return []
    found = []
    for ell in range(1,len(rev)+1):
        for b in range(1,ell):
            if (c[ell],c[b]) not in I.flags or rev[:b] != rev[ell-b:ell]:
                continue
            if all((c[ell-t],c[b-t]) not in I.flags for t in range(1,b+1)):
                found.append(sum(a in letters for a in rev[:b]))
    return found


def finite_language(I):
    """Used only for deliberately forward-acyclic tables."""
    found = []
    todo = [(I.start,'')]
    while todo:
        p,w = todo.pop()
        if p in I.final:
            found.append(w)
        for a,q in enumerate(I.delta[p]):
            if q >= 0:
                assert q > p
                todo.append((q,w+str(a)))
    return found


def graph_checks():
    graphs = cost_cases = lasso_checks = 0
    for n in range(1,4):
        for vector in product(range(n),repeat=2*n):
            raw = [vector[2*p:2*p+2] for p in range(n)]
            live = sorted(reach(raw,[0]))
            ix = {q:p for p,q in enumerate(live)}
            edges = [tuple(ix[q] for q in raw[p]) for p in live]
            reps = [None]*len(edges)
            reps[0] = ''
            todo = deque([0])
            while todo:
                p = todo.popleft()
                for a,q in enumerate(edges[p]):
                    if reps[q] is None:
                        reps[q] = reps[p]+str(a)
                        todo.append(q)
            closure = [reach(edges,[p]) for p in range(len(edges))]
            graphs += 1
            for letters in ('','0','1','01'):
                maximum,longest,cause,comp = weighted_fibres(edges,reps,letters)
                # Independent positive-cycle criterion using all reachability sets.
                infinite = {t for p,row in enumerate(edges) for a,q in enumerate(row)
                            if str(a) in letters and p in closure[q] for t in closure[p]}
                # Every finite-cost walk can drop all zero-cost cycles.
                d = [-1]*len(edges)
                d[0] = 0
                best = d[:]
                for _ in range(len(edges)-1):
                    nd = [-1]*len(edges)
                    for p,row in enumerate(edges):
                        if d[p] >= 0:
                            for a,q in enumerate(row):
                                nd[q] = max(nd[q],d[p]+(str(a) in letters))
                    best = list(map(max,zip(best,nd)))
                    d = nd
                for t in range(len(edges)):
                    if t in infinite:
                        assert maximum[t] is None
                        p = cost_lasso(edges,reps,t,cause,comp)
                        assert sum(a in letters for a in p['loop']) > 0
                        for m in (1,2,4):
                            w = p['prefix']+p['loop']*m+p['suffix']
                            q = 0
                            for a in w:
                                q = edges[q][int(a)]
                            assert q == t
                            lasso_checks += 1
                    else:
                        assert maximum[t] == best[t]
                        w = longest[t]
                        q = 0
                        for a in w:
                            q = edges[q][int(a)]
                        assert q == t and sum(a in letters for a in w) == maximum[t]
                cost_cases += 1
    return dict(graphs=graphs,cost_cases=cost_cases,lasso_checks=lasso_checks)


def acyclic_checks(rng):
    queries = spectra = candidates = 0
    statuses = {'YES':0,'NO':0}
    for _ in range(200):
        k = rng.randint(2,8)
        delta = tuple(tuple(rng.choice([-1]+list(range(p+1,k))) for _ in range(2)) for p in range(k))
        final = frozenset(p for p,row in enumerate(delta) if row == (-1,-1) and rng.random() < .8)
        I = Instance(delta,final,frozenset((p,q) for p in range(k) for q in range(k) if rng.random() < .13),
                     frozenset(p for p in range(k) if rng.random() < .07))
        language = finite_language(I)
        candidates += len(language)
        for H in range(4):
            expected = any(independent_tail(I,w,H) for w in language)
            answer = relaxed_decision(I,H,UNCAPPED)
            assert answer['status'] == ('YES' if expected else 'NO')
            statuses[answer['status']] += 1
            if expected:
                assert independent_tail(I,answer['word'],H)
            queries += 1
        expected = any(border_witness(I,w) for w in language)
        answer = semantic_decision(I,UNCAPPED)
        assert answer['status'] == ('YES' if expected else 'NO')
        for f in sorted(I.final):
            for last in '01':
                part = normalized_slice(I,f,last)
                if part is None:
                    continue
                J,_ = part
                jl = finite_language(J)
                for letters in ('0','1','01'):
                    costs = [x for w in jl for x in all_last_costs(J,w,letters)]
                    out = spectrum_slice(J,letters,UNCAPPED)
                    assert out['status'] == 'FINITE' and out['H'] == max(costs,default=0)
                    spectra += 1
    return dict(instances=200,relaxation_queries=queries,statuses=statuses,
                accepted_candidates=candidates,exact_spectra=spectra,semantic_decisions=200)


def small_terminal_checks():
    count = word_checks = query_checks = 0
    outcomes = {'YES':0,'NO':0,'UNKNOWN':0}
    for k in range(1,4):
        possible = [(p,q) for p in range(k-1) for q in range(k-1) if p != q]
        for raw in product(range(-1,k),repeat=2*(k-1)):
            delta = tuple(tuple(raw[2*p:2*p+2]) for p in range(k-1))+((-1,-1),)
            for mask in range(1 << len(possible)):
                flags = frozenset(p for i,p in enumerate(possible) if mask >> i & 1)
                I = Instance(delta,frozenset({k-1}),flags)
                count += 1
                accepted = [w for w in words('01',6) if I.admissible(w)]
                for H in (0,1,2):
                    for w in accepted:
                        assert tail_safe(I,w,H) == independent_tail(I,w,H)
                        word_checks += 1
                    # Three-state short-word positives are diagnostics, not NO oracles.
                    answer = relaxed_decision(I,H,UNCAPPED)
                    assert answer['status'] in ('YES','NO')
                    if any(independent_tail(I,w,H) for w in accepted):
                        assert answer['status'] == 'YES'
                    if answer['status'] == 'YES':
                        assert independent_tail(I,answer['word'],H)
                    query_checks += 1
                answer = semantic_decision(I,UNCAPPED)
                outcomes[answer['status']] += 1
                if answer['status'] == 'YES':
                    assert witness(I,answer['word']) and border_witness(I,answer['word'])
                if any(border_witness(I,w) for w in accepted):
                    assert answer['status'] != 'NO'
    return dict(instances=count,accepted_word_predicate_checks=word_checks,
                exact_relaxation_calls=query_checks,semantic_outcomes=outcomes,
                negative_oracle_scope='Only complete acyclic languages elsewhere; short words do not certify NO')


def equality_schema_checks():
    """Complete infinite-language oracles via finite equality partitions.

    Each stage has a 1 self-loop and a 0 edge to the next stage. Hit bits are
    always true for a flag (empty data tails); only later block equalities
    guard it. Every equality partition of r lengths has representatives < r.
    """
    cases = queries = tuples = 0
    for r in range(1,5):
        delta = tuple((p+1,p) for p in range(r))+((-1,-1),)
        pairs = [(i,j) for i in range(r) for j in range(i+1,r)]
        vectors = list(product(range(r),repeat=r))
        for mask in range(1 << len(pairs)):
            flags = frozenset(p for i,p in enumerate(pairs) if mask >> i & 1)
            I = Instance(delta,frozenset({r}),flags)
            cases += 1
            for H in range(r+1):
                def good(ns):
                    return not any(r-j <= H and all(ns[i+h] == ns[j+h]
                               for h in range(1,r-j)) for i,j in flags)
                expected = any(good(ns) for ns in vectors)
                answer = relaxed_decision(I,H,UNCAPPED)
                assert answer['status'] == ('YES' if expected else 'NO')
                for ns in vectors:
                    w = ''.join('1'*n+'0' for n in ns)
                    assert independent_tail(I,w,H) == good(ns)
                    tuples += 1
                queries += 1
    return dict(infinite_languages=cases,complete_queries=queries,tuple_formula_checks=tuples)



def fixtures():
    old = Instance(((2,1),(2,1),(-1,3),(4,3),(-1,-1)),frozenset({4}),frozenset({(0,2),(0,3),(1,2)}))
    table = ((2,1),(2,1),(2,3),(2,4),(5,3),(-1,-1))
    flags = frozenset({(0,2),(0,3),(0,4),(1,2)})
    new = Instance(table,frozenset({5}),flags)
    positive = Instance(table,frozenset({5}),flags-{(1,2)})
    seven = Instance(((-1,1),(2,1),(3,-1),(-1,4),(5,4),(6,-1),(-1,-1)),
                     frozenset({6}),frozenset({(0,3),(4,5)}))
    rows = {}
    for name,I,expected in [('old_five',old,'NO'),('nonflat_six',new,'NO'),
                            ('nonflat_positive',positive,'YES'),('different_gap_seven',seven,'NO')]:
        out = semantic_decision(I,UNCAPPED)
        assert out['status'] == expected
        length = spectrum_slice(I,'01',UNCAPPED)
        marker = spectrum_slice(I,'0',UNCAPPED)
        if 'pumping_certificate' in length:
            for m in (1,2,5):
                assert last_aligned(I,**realize(length['pumping_certificate'],m))
        rows[name] = dict(decision=out,length_spectrum=length,marker_spectrum=marker)
    assert rows['nonflat_six']['length_spectrum']['status'] == 'UNBOUNDED'
    assert rows['nonflat_six']['marker_spectrum']['H'] == 1
    unique = budgets = 0
    for n in range(1,32,2):
        w = '1'*n+'0'+'1'*(n+1)+'0'
        c = new.run(w)
        actual = [(i,j) for i in range(len(w)+1) for j in range(i,len(w)+1)
                  if (c[i],c[j]) in new.flags and w[i:].startswith(w[j:])]
        assert actual == [(0,n+2)]
        unique += 1
        for L in range(8):
            for D in range(8):
                assert necessary(new,w,L,D) == (n+1 > L and n+2 > D)
                budgets += 1
    for L,D in ((0,0),(1,1),(2,2),(4,3),(3,5)):
        assert Sandwich(new,L,D).search()['status'] == 'YES'
    # A precise incompleteness obstruction: exact boundary-aligned uniform code.
    encoded = uniform_code(old)
    for H in range(6):
        n = H+1
        w = '1'*n+'0'+'1'*(n+1)+'0'
        ew = ''.join('00' if a == '0' else '10' for a in w)
        assert not border_witness(encoded,ew) and independent_tail(encoded,ew,H)
    unresolved = semantic_decision(encoded,UNCAPPED)
    assert unresolved['status'] == 'UNKNOWN'
    rows['encoded_obstruction'] = unresolved
    return dict(examples=rows,unique_violation_checks=unique,necessary_identity_checks=budgets,
                complete_necessary_graphs=5,encoded_relaxation_survivors=6),new,positive


def uniform_code(I):
    k = len(I.delta)
    table = []
    for p in range(k):
        # intermediate state k+q carries the destination reached after the final 0
        table.append((k+I.delta[p][0] if I.delta[p][0] >= 0 else -1,
                      k+I.delta[p][1] if I.delta[p][1] >= 0 else -1))
    table.extend((q,-1) for q in range(k))
    return Instance(tuple(table),I.final,I.flags,I.bad,I.start)


def cap_checks(I,positive):
    guards = 0
    for name,value in [('states',1),('steps',1),('schemas',1),('descriptors',1),('blocks',1)]:
        caps = dict(UNCAPPED.__dict__,**{name:value})
        H = 2 if name == 'blocks' else 1
        ans = relaxed_decision(positive,H,Limits(**caps))
        assert ans['status'] == 'UNKNOWN',(name,ans)
        guards += 1
    for field in ('monoid','combinations'):
        caps = dict(UNCAPPED.__dict__,**{field:1})
        assert spectrum_slice(I,'0',Limits(**caps))['status'] == 'UNKNOWN'
        guards += 1
    for value in (True,-1,1.5):
        try:
            relaxed_decision(I,value)
            raise AssertionError('Invalid bound accepted')
        except ValueError:
            guards += 1
    try:
        semantic_decision(Instance(((0,0),),frozenset({0})))
        raise AssertionError('Nonterminal input accepted')
    except ValueError:
        guards += 1
    return guards


def main():
    rng = random.Random(SEED)
    result = dict(seed=SEED,status='PASS')
    result['weighted_graphs'] = graph_checks()
    result['acyclic'] = acyclic_checks(rng)
    result['small_terminal'] = small_terminal_checks()
    result['equality_schemas'] = equality_schema_checks()
    fixed,no,yes = fixtures()
    result['fixtures'] = fixed
    result['scope_and_cap_guards'] = cap_checks(no,yes)
    result['proof_status'] = 'Written all-length proofs; independent mathematical review pending; not Lean-checked'
    result['scope'] = 'Exact fixed-marker-tail relaxation and finite-marker-spectrum class, not unrestricted Problem 1.7'
    out = Path(__file__).resolve().parents[1]/'results'/'semantic-marker-tails.json'
    out.parent.mkdir(exist_ok=True)
    out.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'fixtures'},sort_keys=True,indent=2))


if __name__ == '__main__':
    main()
