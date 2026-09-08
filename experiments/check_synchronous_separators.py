"""Independent checks for synchronous-separator preprocessing."""
from itertools import product
import json
from pathlib import Path

from border_lab import Instance, border_witness, witness, words
from marker_certificate import marker_decision
from synchronous_separators import (compile_separators, encode_word,
                                    separator_certificate, separator_decision)


def uniform_code(I):
    """Exact fixed-length code C(0)=00, C(1)=10 used by the marker obstruction."""
    k = len(I.delta)
    table = []
    for p in range(k):
        table.append((k + I.delta[p][0] if I.delta[p][0] >= 0 else -1,
                      k + I.delta[p][1] if I.delta[p][1] >= 0 else -1))
    table.extend((q, -1) for q in range(k))
    return Instance(tuple(table), I.final, I.flags, I.bad, I.start)


def check_equivalence(I, maximum):
    summary, cert = separator_certificate(I)
    if cert is None:
        return 0
    J = compile_separators(I, cert)
    count = 0
    for w in words('01', maximum):
        if I.run(w) is None:
            continue
        ew = encode_word(I, w, cert)
        assert I.admissible(w) == J.admissible(ew)
        assert witness(I, w) == witness(J, ew)
        assert border_witness(I, w) == border_witness(J, ew)
        count += 1
    return count


def small_census():
    instances = certified = comparisons = yes = no = unknown = 0
    for k in range(1, 4):
        possible = [(p, q) for p in range(k-1) for q in range(k-1) if p != q]
        for raw in product(range(-1, k), repeat=2*(k-1)):
            delta = tuple(tuple(raw[2*p:2*p+2]) for p in range(k-1)) + ((-1, -1),)
            for mask in range(1 << len(possible)):
                flags = frozenset(pair for i, pair in enumerate(possible) if mask >> i & 1)
                I = Instance(delta, frozenset({k-1}), flags)
                instances += 1
                summary, cert = separator_certificate(I)
                if cert is None:
                    unknown += 1
                    continue
                certified += 1
                comparisons += check_equivalence(I, 6)
                out = separator_decision(I, max_schemas=None, max_states=None,
                                         max_transitions=None)
                assert out['status'] in ('YES', 'NO')
                if out['status'] == 'YES':
                    assert witness(I, out['word']) and border_witness(I, out['word'])
                    yes += 1
                else:
                    no += 1
    return dict(instances=instances, certified=certified,
                uncertified=unknown, word_equivalence_checks=comparisons,
                exact_yes=yes, exact_no=no)


def encoded_obstruction():
    old = Instance(((2,1),(2,1),(-1,3),(4,3),(-1,-1)), frozenset({4}),
                   frozenset({(0,2),(0,3),(1,2)}))
    encoded = uniform_code(old)
    # Raw-marker tails deliberately fail on this instance. The synchronous
    # colouring discovers the latent original-zero separator structure.
    summary, cert = separator_certificate(encoded)
    assert cert is not None
    assert cert.marked == frozenset({(0,0),(1,0),(3,0)})
    compiled = compile_separators(encoded, cert)
    direct = marker_decision(compiled, max_schemas=None, max_states=None,
                             max_transitions=None)
    assert direct['status'] == 'NO'
    answer = separator_decision(encoded, max_schemas=None, max_states=None,
                                max_transitions=None)
    assert answer['status'] == 'NO'
    # The five-state source is also certified directly.
    source = separator_decision(old, max_schemas=None, max_states=None,
                                max_transitions=None)
    assert source['status'] == 'NO'
    comparisons = check_equivalence(encoded, 12)
    return dict(source_status=source['status'], encoded_status=answer['status'],
                marked=summary['marked'], compiled_states=len(compiled.delta),
                equivalence_checks=comparisons,
                downstream_schemas=direct['schemas'])


def conflict_fixture():
    # Flag (0,1) synchronizes the terminal 1-edge from state 1 with the 1-loop
    # at state 0. The former must be a separator and the latter must be data.
    I = Instance(((1,0),(-1,2),(-1,-1)), frozenset({2}), frozenset({(0,1)}))
    summary, cert = separator_certificate(I)
    assert cert is None and summary['status'] == 'NOT_APPLICABLE'
    assert separator_decision(I)['status'] == 'UNKNOWN'
    return summary


def main():
    result = {'status': 'PASS', 'small_census': small_census(),
              'encoded_obstruction': encoded_obstruction(),
              'conflict_fixture': conflict_fixture(),
              'scope': 'Exact on synchronous-separator certified terminal instances only',
              'proof_status': 'Written proof + reproducible checks; independent mathematical review pending; not newly Lean-checked'}
    path = Path(__file__).resolve().parents[1] / 'results' / 'synchronous-separators.json'
    path.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
