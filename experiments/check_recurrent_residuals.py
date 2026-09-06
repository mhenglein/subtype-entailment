"""Reproduce the recurrent-reference collision and exact symbolic kernel.

All-length claims have separate proofs. The enumeration below checks the
implementation, not unrestricted decidability or a conjectured stopping bound.
"""
from dataclasses import replace
from hashlib import sha1
from itertools import product
import json
from pathlib import Path
from border_lab import Instance, words, witness, border_witness
from recurrent_residuals import (
    TABLE, EQUALITY_FLAGS, BOUNDARY, PROPER, REPRESENTATIVES,
    instance, encode, parse_candidate, symbolic_profile, direct_profile,
    transition_action, reference_summary, residual_membership,
    decide_kernel, symbolic_exists, copy_instance, encode_data, copy_candidate,
    parse_copy_candidate, copy_residual_membership,
)
from terminal_realization import realize
from denial_bridge import Canonical

ROOT = Path(__file__).resolve().parents[1]


def reverse_profile(I, w):
    run = I.run(w)
    assert run is not None
    rho, c = w[::-1], run[::-1]
    return frozenset((c[m], c[b]) for m in range(len(w)+1)
                     for b in range(m+1) if rho[:b] == rho[m-b:m])


def subset(items, mask):
    return frozenset(value for j, value in enumerate(items) if mask >> j & 1)


def run():
    counts = dict(raw_words=0, raw_candidates=0, count_vectors=0,
                  suffix_summaries=0, residual_word_checks=0,
                  context_matrix_checks=0, effective_flag_sets=0,
                  flag_bad_combinations=0, irrelevant_flag_extensions=0,
                  canonical_paths=0, guards=0, copy_raw_words=0,
                  copy_tuples=0, copy_residual_checks=0, strong_collisions=0)
    I = instance()
    for w in words('01', 14):
        parsed = parse_candidate(w)
        assert I.admissible(w) == (parsed is not None)
        assert witness(I, w) == border_witness(I, w)
        counts['raw_words'] += 1
        if parsed:
            m, z, n = parsed
            assert direct_profile(I, w) == reverse_profile(I, w) == symbolic_profile(m, z, n)
            assert witness(I, w) == (m == n)
            counts['raw_candidates'] += 1
    for m, z, n in product(range(1, 17), range(1, 5), range(1, 17)):
        w = encode(m, z, n)
        assert direct_profile(I, w) == reverse_profile(I, w) == symbolic_profile(m, z, n)
        assert witness(I, w) == border_witness(I, w) == (m == n)
        counts['count_vectors'] += 1
    expected_summary = reference_summary(1)
    for n in range(1, 65):
        assert reference_summary(n) == expected_summary
        counts['suffix_summaries'] += 1
    for n in range(1, 9):
        v = '1'*n+'0'
        for x in words('01', 10):
            run_x = I.run(x)
            actual = run_x is not None and run_x[-1] == 2 and witness(I, x+v)
            assert actual == residual_membership(x, n)
            counts['residual_word_checks'] += 1
    for m, n in product(range(1, 33), repeat=2):
        x, v = '1'*m+'0', '1'*n+'0'
        assert witness(I, x+v) == border_witness(I, x+v) == (m == n)
        counts['context_matrix_checks'] += 1

    # Only these 14 pairs occur in any candidate profile; exhaust all their
    # combinations. For each, the 32 Bad sets cover every safety annotation.
    effective = tuple(sorted(BOUNDARY | PROPER))
    assert len(effective) == 14
    census = {'YES': 0, 'NO': 0}
    for mask in range(1 << len(effective)):
        G = subset(effective, mask)
        J = instance(G)
        exact = symbolic_exists(G)
        independent = any(witness(J, w) for w in REPRESENTATIVES)
        assert exact == independent
        ans = decide_kernel(J)
        assert (ans['status'] == 'YES') == exact
        census[ans['status']] += 1
        counts['effective_flag_sets'] += 1
        for bad_mask in range(32):
            bad = subset(tuple(range(5)), bad_mask)
            K = replace(J, bad=bad)
            answer = decide_kernel(K)
            assert (answer['status'] == 'YES') == symbolic_exists(G, bad)
            assert (answer['status'] == 'YES') == any(border_witness(K, w) for w in REPRESENTATIVES)
            counts['flag_bad_combinations'] += 1
    irrelevant = tuple(sorted(set(product(range(5), repeat=2)) - set(effective)))
    assert len(irrelevant) == 11
    bases = (frozenset(), EQUALITY_FLAGS, frozenset({(1, 3)}),
             frozenset({(0, 2), (0, 3), (1, 2)}))
    for base in bases:
        for mask in range(1 << len(irrelevant)):
            G = base | subset(irrelevant, mask)
            ans = decide_kernel(instance(G))
            assert (ans['status'] == 'YES') == symbolic_exists(base)
            counts['irrelevant_flag_extensions'] += 1

    # Exact regular-model operations from the existing bridge. These checks
    # inherit the bridge's recorded status and are not a new semantic proof.
    R = realize(I)
    for m, z, n in product(range(1, 4), range(1, 3), range(1, 4)):
        w = encode(m, z, n)
        errors = Canonical(R.variables, R.constraints, R.alpha, R.beta, w).errors()
        assert (not errors) == (m == n)
        counts['canonical_paths'] += 1
    assert decide_kernel(Instance(((0, 0),), frozenset({0})))['status'] == 'UNKNOWN'
    counts['guards'] += 1
    for args in ((0, 1, 1), (1, -1, 1), (1, 1, True)):
        try:
            symbolic_profile(*args)
            raise AssertionError('Missing count guard')
        except ValueError:
            counts['guards'] += 1
    huge = 10**100
    assert symbolic_profile(huge, huge, huge) == symbolic_profile(1, 2, 1)
    assert symbolic_profile(huge, 1, huge+1) == symbolic_profile(1, 1, 2)
    # A naive collision merge can give either error depending on its representative.
    assert witness(I, '10'+'10') and not witness(I, '10'+'110')
    assert witness(I, '110'+'110') and not witness(I, '110'+'10')

    # A second fixture tests actual word content, not only an omitted length.
    C = copy_instance()
    for w in words('01', 16):
        parsed = parse_copy_candidate(w)
        assert C.admissible(w) == (parsed is not None)
        expected = parsed is not None and parsed[0] == parsed[2]
        assert witness(C, w) == border_witness(C, w) == expected
        counts['copy_raw_words'] += 1
    data = tuple(words('01', 3))
    for left, right, returns in product(data, data, range(4)):
        w = copy_candidate(left, right, returns)
        assert parse_copy_candidate(w) == (left, returns, right)
        assert witness(C, w) == border_witness(C, w) == (left == right)
        counts['copy_tuples'] += 1
    for u in words('01', 2):
        v = encode_data(u)+'00'
        for x in words('01', 10):
            state = C.run(x)
            expected = state is not None and state[-1] == 5 and witness(C, x+v)
            assert expected == copy_residual_membership(x, u)
            counts['copy_residual_checks'] += 1
    # Same length, letter counts, first/last bits, full action, visited set,
    # exact agreement profile, and intrinsic sufficient budget; different
    # reference contents still cannot be merged.
    from border_lab import word_budget, lrs
    J = replace(C, start=5)
    us = ('0100', '0010')
    vs = tuple(encode_data(u)+'00' for u in us)
    def rich_signature(v):
        c = J.run(v)
        return (len(v), v.count('0'), v.count('1'), v[0], v[-1],
                frozenset(c), transition_action(J, v), direct_profile(J, v),
                word_budget(J, v), lrs(v))
    signature = rich_signature(vs[0])
    assert signature == rich_signature(vs[1])
    for p in range(2):
        for q in range(2):
            assert witness(C, vs[p]+vs[q]) == border_witness(C, vs[p]+vs[q]) == (p == q)
            counts['strong_collisions'] += 1
    CR = realize(C)
    for left, right, returns in (('', '', 0), ('0', '1', 0),
                                 ('0100', '0100', 1), ('0100', '0010', 1)):
        w = copy_candidate(left, right, returns)
        assert (not Canonical(CR.variables, CR.constraints, CR.alpha, CR.beta, w).errors()) == (left == right)
        counts['canonical_paths'] += 1

    def git_blob(name):
        raw = (ROOT/'experiments'/name).read_bytes()
        return sha1(('blob %d\0' % len(raw)).encode()+raw).hexdigest()
    return dict(
        status='PASS', base_main='bd4fde8f986a843fbc6f7b6f7ca626a5d0f67b0f',
        counts=counts, effective_flag_census=census,
        witness_language='1^m 0^z 1^m 0, m>=1,z>=1',
        residual_language='R_n = 1^n 0^+, n>=1; pairwise disjoint and nonempty',
        common_suffix_summary=dict(start=2, final=4, visited=[2,3,4],
            action=list(expected_summary[3]), profile=sorted(expected_summary[4])),
        collision=dict(suffixes=['10','110'], common_prefix='10',
                       concatenations=['1010','10110'], witness_verdicts=[True,False]),
        complete_existence_basis=list(REPRESENTATIVES),
        copy_family=dict(states=len(C.delta), flags=sorted(C.flags),
            witness_language='E(u)00(01)^a E(u)00, a>=0; E(0)=10,E(1)=11',
            residual_language='R_u = E(u)00(01)*',
            same_length_collision=dict(data=us,suffixes=vs,
                raw_length=signature[0],letter_counts=[signature[1],signature[2]],
                action=signature[6],profile=sorted(signature[7]),
                word_budget=signature[8],lrs=signature[9],
                common_prefix=vs[0],witness_verdicts=[True,False]),
            subtype_variables=CR.variables,subtype_constraints=len(CR.constraints)),
        subtype_realization=dict(variables=R.variables, constraints=len(R.constraints)),
        dependency_git_blobs={name:git_blob(name) for name in
            ('border_lab.py','terminal_realization.py','denial_bridge.py')},
        proof_status='Written all-length proofs; independent review pending; not Lean-checked',
        limits='Kernel-specific exact existence. Finite suffix summaries and literal residual inclusion fail; unrestricted decidability is not determined.')


if __name__ == '__main__':
    result = run()
    (ROOT/'results/recurrent-residuals.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))
