"""Issue #23: executable transfer contracts, not a new unrestricted solver.

Uses a complete finite-valuation oracle ONLY for systems whose own acyclic
upper constraints prove a finite model-height bound. Existing proof/solver
sources are pinned and unmodified. Other terminal instances remain UNKNOWN
unless the supplied exact acyclic oracle applies.
"""
from collections import Counter, deque
from dataclasses import replace
from functools import lru_cache
from itertools import product
from pathlib import Path
import argparse
import hashlib
import json
import random

from border_lab import Instance, witness, border_witness
from denial_bridge import build, Canonical
from infinite_extensions import infinite_extension_decision
from safe_extensions import absorption_holds

ROOT = Path(__file__).resolve().parents[1]
BASE = '35bff158f4620224f2608ba7bccf5ab770811853'
DEPS = {
    'border_lab.py': '1144ae52379e0417772e79582269cacd91c5bc17',
    'denial_bridge.py': 'a38a21df533d8853aa34b3b2593d164a4a688447',
    'infinite_extensions.py': 'eda28ac44cbfe969a5aa83b2cade036b0f171fdc',
    'safe_extensions.py': '866b04fa67fa14684e56db75ce6cd850dff82009',
}


def blob(path):
    b = path.read_bytes()
    return hashlib.sha1(b'blob ' + str(len(b)).encode() + b'\0' + b).hexdigest()


def check_dependencies():
    observed = {name: blob(ROOT/'experiments'/name) for name in DEPS}
    if observed != DEPS:
        raise RuntimeError('Reviewed dependencies changed; re-audit before updating hashes')
    return observed


def safe(I):
    return set(range(len(I.delta))) - set(I.bad) - {p for p, q in I.flags if p == q}


def terminal_restriction(I):
    """C031: same state labels, same flags; prune BEFORE selecting final sinks."""
    allowed = safe(I)
    delta = tuple(tuple(q if p in allowed and q in allowed else -1 for q in row)
                  for p, row in enumerate(I.delta))
    finals = frozenset(p for p in I.final if p in allowed and all(q < 0 for q in delta[p]))
    return replace(I, delta=delta, final=finals)


def complete_acyclic_terminal_oracle(I):
    """An exact oracle on a checked DAG only; cycles return scoped UNKNOWN."""
    if any(q >= 0 for p in I.final for q in I.delta[p]):
        raise ValueError('Terminal accepting states required')
    allowed = safe(I)
    if I.start not in allowed:
        return {'status': 'NO', 'candidates': 0}
    reached = {I.start}
    queue = [I.start]
    for p in queue:
        for q in I.delta[p]:
            if q in allowed and q not in reached:
                reached.add(q); queue.append(q)
    indegree = {p: 0 for p in reached}
    for p in reached:
        for q in I.delta[p]:
            if q in reached: indegree[q] += 1
    todo = deque(p for p in reached if indegree[p] == 0)
    removed = 0
    while todo:
        p = todo.popleft(); removed += 1
        for q in I.delta[p]:
            if q in reached:
                indegree[q] -= 1
                if not indegree[q]: todo.append(q)
    if removed != len(reached):
        return {'status': 'UNKNOWN', 'reason': 'Oracle only covers acyclic safe graphs'}
    todo = [(I.start, '')]; count = 0
    while todo:
        p, w = todo.pop()
        if p in I.final:
            count += 1
            a = witness(I, w)
            assert a == border_witness(I, w)
            if a: return {'status': 'YES', 'word': w, 'candidates': count}
        for a, q in zip('01', I.delta[p]):
            if q in reached: todo.append((q, w+a))
    return {'status': 'NO', 'candidates': count}


def merge_evidence(satisfiability, infinite=None, terminal=None):
    """Typed logical truth table. Callers must validate YES certificates."""
    if satisfiability == 'UNSAT': return 'ENTAILED'
    if satisfiability != 'SAT': return 'UNKNOWN'
    if infinite == 'YES' or terminal == 'YES': return 'NOT_ENTAILED'
    if infinite == 'NO_INFINITE_EXTENSION' and terminal == 'NO': return 'ENTAILED'
    return 'UNKNOWN'


def check_transfer(n, constraints, alpha, beta, terminal_oracle=complete_acyclic_terminal_oracle,
                   max_classes=None):
    # n+n+(n+1) bits in the three subset components. This is a guaranteed
    # sufficient capacity, NOT a guessed non-entailment search cutoff.
    cap = (1 << (3*n+1)) if max_classes is None else max_classes
    status, B = build(n, constraints, alpha, beta, max_classes=cap)
    if status != 'SAT': return {'status': merge_evidence(status), 'build': status}
    I = B.instance
    assert absorption_holds(I)
    k = len(I.delta)
    # A fixed primitive period d<=k has at most 2*k*d*2^(k*d)
    # monitor states. A single maximum covers every such d.
    monitor_cap = 2*k*k*(1 << (k*k))
    ext = infinite_extension_decision(I, max_states=monitor_cap)
    if ext['status'] == 'YES':
        w = ext['word']
        assert witness(I, w) and border_witness(I, w)
        return {'status': 'NOT_ENTAILED', 'branch': 'infinite', 'word': w, 'states': k}
    J = terminal_restriction(I)
    ans = terminal_oracle(J)
    if ans['status'] == 'YES':
        w = ans['word']
        assert witness(J, w) and witness(I, w) and border_witness(I, w)
    outcome = merge_evidence('SAT', ext['status'], ans['status'])
    out = {'status': outcome, 'build': 'SAT', 'infinite': ext['status'],
           'terminal': ans['status'], 'states': k}
    if ans['status'] == 'YES': out.update(word=ans['word'], branch='terminal')
    return out


@lru_cache(None)
def tree_sets(height):
    """All product-address sets with height at most height; includes bottom."""
    if height == 0: return (frozenset(),)
    out = [frozenset()]
    for x, y in product(tree_sets(height-1), repeat=2):
        out.append(frozenset({''} | {'0'+w for w in x} | {'1'+w for w in y}))
    return tuple(out)


def pair(x, y):
    return frozenset({''} | {'0'+w for w in x} | {'1'+w for w in y})


def satisfies(values, constraints):
    for c in constraints:
        if c[0] == 'leq' and not values[c[1]] <= values[c[2]]: return False
        if c[0] == 'upper' and not values[c[1]] <= pair(values[c[2]], values[c[3]]): return False
        if c[0] == 'lower' and not pair(values[c[1]], values[c[2]]) <= values[c[3]]: return False
        if c[0] == 'denial' and values[c[1]]: return False
    return True


def finite_models(n, constraints):
    """Caller supplies acyclic upper backbone; verify its bound explicitly.

    Every non-bottom variable has an upper product into larger indices, and
    variable n-1 is denied. Descending induction bounds height, independently
    of all additional constraints. Enumeration is therefore complete for all
    arbitrary-tree valuations of THESE systems, not a guessed approximation.
    """
    uppers = {c[1]: c[2:] for c in constraints if c[0] == 'upper'}
    assert ('denial', n-1) in constraints
    h = {n-1: 0}
    for p in reversed(range(n-1)):
        l, r = uppers[p]
        assert p < l < n and p < r < n
        h[p] = 1+max(h[l], h[r])
    candidates = list(product(*(tree_sets(h[p]) for p in range(n))))
    return [v for v in candidates if satisfies(v, constraints)], len(candidates), h


def eps_closure(n, cs, q):
    seen={q}; todo=[q]
    for p in todo:
        for c in cs:
            if c[0]=='leq' and c[1]==p and c[2] not in seen:
                seen.add(c[2]);todo.append(c[2])
    return seen


def check():
    deps = check_dependencies(); rng=random.Random(2026091823)
    counts=Counter(); outcomes=Counter(); fixtures=[]
    max_states=0
    # Complete arbitrary-tree oracle, because each input proves its finite bound.
    for n in (3,4):
        for trial in range(100):
            base=[('upper', p, rng.randrange(p+1,n), rng.randrange(p+1,n)) for p in range(n-1)]
            base.append(('denial',n-1))
            extra=[]
            for _ in range(rng.randrange(0,5)):
                kind=rng.choice(('leq','lower','denial'))
                arity={'leq':2,'lower':3,'denial':1}[kind]
                extra.append((kind,*(rng.randrange(n) for _ in range(arity))))
            cs=tuple(base+extra)
            models, nvals, heights=finite_models(n,cs)
            counts['bounded_input_systems']+=1
            counts['all_valuations_examined']+=nvals
            counts['satisfying_valuations']+=len(models)
            counts['satisfiable_systems' if models else 'unsatisfiable_systems']+=1
            for a,b in product(range(n),repeat=2):
                expected=all(v[a]<=v[b] for v in models)
                out=check_transfer(n,cs,a,b)
                counts['complete_arbitrary_tree_queries']+=1
                outcomes[out['status']]+=1
                max_states=max(max_states,out.get('states',0))
                assert out['status']==('ENTAILED' if expected else 'NOT_ENTAILED'),(cs,a,b,out,heights)
                if not expected:
                    w=out['word']
                    assert any(w in v[a] and w not in v[b] for v in models)
                    counts['witness_addresses_checked_against_all_models']+=1
                    if counts['exact_regular_countermodels']<32:
                        assert not Canonical(n,cs,a,b,w).errors()
                        counts['exact_regular_countermodels']+=1
    # No lower-product constraints: epsilon closure is a complete independent
    # all-tree entailment oracle. Empty models satisfy; a root-only valuation
    # provides a countermodel unless alpha is denied or beta is epsilon-reached.
    n=2; leqs=[('leq',p,q) for p,q in product(range(n),repeat=2)]
    uppers=[('upper',p,q,r) for p,q,r in product(range(n),repeat=3)]
    for mask in range(16):
        for denied in range(4):
            for u in (None,*uppers):
                cs=tuple([leqs[i] for i in range(4) if mask>>i&1]+
                         [('denial',i) for i in range(n) if denied>>i&1]+([] if u is None else [u]))
                for a,b in product(range(n),repeat=2):
                    reached=eps_closure(n,cs,a)
                    expected=(b in reached or any(denied>>q&1 for q in reached))
                    out=check_transfer(n,cs,a,b)
                    assert out['status']==('ENTAILED' if expected else 'NOT_ENTAILED'),(cs,a,b,out)
                    counts['no_lower_exact_queries']+=1
    # Source semantics: an explicit regular infinite model, not finite trees.
    cs=(('lower',0,1,0),('denial',1))
    out=check_transfer(2,cs,0,1)
    assert out['status']=='NOT_ENTAILED' and out['branch']=='infinite'
    # C029 promises a witness, not the shortest witness; epsilon is checked separately.
    C=Canonical(2,cs,0,1,'');assert not C.errors()
    # Check exact 0* using subset product against a two-state literal DFA.
    todo=[(C.start(0),0)];seen=set(todo)
    for x,q in todo:
        assert (C.final in x)==(q==0)
        for a in (0,1):
            t=(C.nfa.step(x,a),0 if q==0 and a==0 else 1)
            if t not in seen:seen.add(t);todo.append(t)
    counts['infinite_model_language_product_states']=len(seen)
    fixtures.append({'name':'infinite_spine','answer':out,'model':'X(0)=0*, X(1)=empty; no finite model'})
    # Three-valued composition and contradictory-scope guards.
    for s in ('UNSAT','SAT','UNKNOWN'):
        for inf in ('YES','NO_INFINITE_EXTENSION','UNKNOWN'):
            for ter in ('YES','NO','UNKNOWN'):
                got=merge_evidence(s,inf,ter)
                expected=('ENTAILED' if s=='UNSAT' else 'UNKNOWN' if s!='SAT' else
                          'NOT_ENTAILED' if 'YES' in (inf,ter) else
                          'ENTAILED' if inf=='NO_INFINITE_EXTENSION' and ter=='NO' else 'UNKNOWN')
                assert got==expected;counts['status_compositions']+=1
    assert merge_evidence('SAT','NO_INFINITE_EXTENSION','UNKNOWN')=='UNKNOWN'
    assert merge_evidence('SAT','UNKNOWN','YES')=='NOT_ENTAILED'
    assert merge_evidence('SAT','UNKNOWN','NO')=='UNKNOWN'
    # Forced-root UNSAT must short circuit before terminal calls.
    def forbidden_callback(I):raise AssertionError('UNSAT must short circuit')
    out=check_transfer(1,(('lower',0,0,0),('denial',0)),0,0,forbidden_callback)
    assert out['status']=='ENTAILED' and out['build']=='UNSAT'
    fixtures.append({'name':'unsat_short_circuit','answer':out})
    cap=check_transfer(2,(('upper',0,1,1),('denial',1)),0,1,max_classes=1)
    assert cap['status']=='UNKNOWN';fixtures.append({'name':'summary_cap','answer':cap})
    # Final closure alone is insufficient: epsilon good, only safe-sink word bad.
    I=Instance(((1,-1),(-1,-1)),frozenset({0,1}),frozenset({(0,1)}))
    J=terminal_restriction(I)
    assert witness(I,'') and not witness(I,'0') and not absorption_holds(I)
    assert complete_acyclic_terminal_oracle(J)['status']=='NO'
    fixtures.append({'name':'final_absorption_without_empty_columns_is_unsound',
                     'delta':I.delta,'final':sorted(I.final),'flags':sorted(I.flags),
                     'original_witness':'','terminal_result':'NO'})
    # Prune unsafe successors BEFORE computing sinks.
    I=Instance(((1,-1),(-1,-1)),frozenset({0}),bad=frozenset({1}))
    J=terminal_restriction(I)
    assert witness(I,'') and witness(J,'') and J.final==frozenset({0})
    fixtures.append({'name':'prune_before_sinks','original_final':0,'unsafe_successor':1,'word':''})
    # Never promote a nonfinal sink.
    I=Instance(((-1,-1),(-1,-1)),frozenset({1}))
    J=terminal_restriction(I)
    assert complete_acyclic_terminal_oracle(J)['status']=='NO'
    assert witness(replace(J,final=frozenset({0,1})), '')
    fixtures.append({'name':'nonfinal_sink_not_promoted','correct':'NO','incorrect_word':''})
    # C029 negative is not full negative: upper bounds force a finite-only witness.
    cs=(('upper',0,1,1),('denial',1))
    out=check_transfer(2,cs,0,1)
    assert out['status']=='NOT_ENTAILED' and out['infinite']=='NO_INFINITE_EXTENSION' and out['terminal']=='YES'
    fixtures.append({'name':'terminal_only_witness','answer':out})
    # A source of epsilon safety tests is needed; an unsafe original start stays unsafe.
    I=Instance(((-1,-1),),frozenset({0}),bad=frozenset({0}))
    assert not witness(terminal_restriction(I),'')
    counts['explicit_contract_fixtures']=len(fixtures)+1
    return {'status':'PASS','seed':2026091823,'base':BASE,'dependency_blobs':deps,
            'counts':dict(sorted(counts.items())),'bounded_query_verdicts':dict(outcomes),
            'largest_observed_summary':max_states,'fixtures':fixtures,
            'scope':'Transfer-interface regression; no unrestricted terminal solver, no Lean proof, no new memo reread',
            'finite_model_oracle_completeness':'Acyclic upper bounds plus denial prove model-height bounds from each input'}


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=ROOT/'results/semantic-bridge-audit.json')
    args=parser.parse_args()
    if not __debug__:parser.error('Assertions must remain enabled')
    out=check();text=json.dumps(out,indent=2,sort_keys=True)+'\n'
    args.output.parent.mkdir(parents=True,exist_ok=True);args.output.write_text(text)
    print(text)
