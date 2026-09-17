#!/usr/bin/env python3
"""Audit shared-strip diagram substitution on concrete finite instances.

A satisfying diagram is extracted from one reference graph. Different reference
words and monotone embeddings of ALL shared marks are tested against that same
diagram. Successful substitutions must preserve every queried path jointly.
This does not implement the all-input query-preimage compiler.
"""
from collections import Counter
from itertools import combinations, product
from pathlib import Path
import argparse, json, random
from border_lab import Instance
from rank_query_prefix import Reference
from rank_query_graphs import (Automaton, Graph, EDGE_LABELS, first_return,
    local_extension, query_path, path_diagram, forward_observer)
from check_rank_query_graphs import random_observer

ROOT = Path(__file__).resolve().parents[1]


def substitute(I, B, C, G, origin, queries, diagrams, C2, G2, origin2, mapping):
    """Sufficient diagram constraints; no query search on G2 occurs here.

    Core paths and product-state boundary choices remain fixed. Only forward
    pieces may use new lengths. The same mapping/word is used by all queries.
    """
    m = len(B.word)
    if C.word[m] != C2.word[m]:
        return False
    for old, new in mapping.items():
        if G.colours[old] != G2.colours[new]:
            return False
        if origin[old - m - 1] != origin2[new - m - 1]:
            return False
    at = lambda v: v if v <= m else mapping[v]
    for (A, source, target), diagram in zip(queries, diagrams):
        if not diagram['pieces']:
            if at(source) != at(target) or A.start not in A.finals:
                return False
            if not A.permits(A.start, G2.colours[at(source)]):
                return False
        for piece in diagram['pieces']:
            u, q = piece['start']; v, p = piece['end']
            if piece['kind'] == 'forward':
                if p not in forward_observer(G2, A, at(u), at(v), frozenset({q})):
                    return False
            else:
                for old_u, old_q, a, old_v, old_p in piece['edges']:
                    # Core and portal edges are not replaced by independent paths.
                    if (at(old_u), a, at(old_v)) not in G2.edges:
                        return False
                    if not A.permits(old_q, G2.colours[at(old_u)]):
                        return False
                    if not A.permits(old_p, G2.colours[at(old_v)]):
                        return False
    return True


def check():
    rng = random.Random(2026091532)
    counts = Counter()
    I = Instance(((0, 0),), frozenset())
    groups = []
    for b in ('0', '1', '01', '10', '00', '11'):
        B = Reference(b, (0,) * (len(b) + 1))
        cases = []
        for n in range(len(b) + 1, 10):
            for ext in product('01', repeat=n - len(b)):
                c = b + ''.join(ext)
                if not first_return(b, c):
                    continue
                C = Reference(c, (0,) * (n + 1))
                G, origins = local_extension(I, B, C, require_safe=False)
                cases.append((C, G, origins))
        groups.append((B, cases))
    concrete_examples = []
    for trial in range(320):
        B, candidates = rng.choice(groups)
        C, G, origins = rng.choice(candidates)
        m, n = len(B.word), len(C.word)
        queries, diagrams = [], []
        # Several independent paths whose word and all mark positions are shared.
        for _ in range(3):
            A = random_observer(rng, rng.randrange(1, 4))
            for attempt in range(8):
                s = rng.randrange(n + 1); t = rng.randrange(n + 1)
                path = query_path(G, A, s, t)
                if path is not None:
                    queries.append((A, s, t))
                    diagrams.append(path_diagram(G, m, A, s, t, path))
                    break
        if not queries:
            continue
        marks = sorted(set().union(*(set(d['marked_positions']) for d in diagrams)))
        assert marks[0] == m + 1 and marks[-1] == n
        identity = {j: j for j in marks}
        assert substitute(I, B, C, G, origins, queries, diagrams, C, G, origins, identity)
        counts['original_joint_diagrams'] += 1
        counts['joint_query_atoms'] += len(queries)
        for C2, G2, origins2 in rng.sample(candidates, min(18, len(candidates))):
            n2 = len(C2.word)
            if len(marks) == 1:
                choices = [(m + 1,)] if n2 == m + 1 else []
            elif n2 - m >= len(marks):
                choices = ((m + 1,) + inner + (n2,)
                           for inner in combinations(range(m + 2, n2), len(marks) - 2))
            else:
                choices = []
            for index, chosen in enumerate(choices):
                if index >= 80:
                    break  # finite test selection, never a decision cutoff
                mapping = dict(zip(marks, chosen))
                counts['candidate_graft_assignments'] += 1
                if not substitute(I, B, C, G, origins, queries, diagrams,
                                  C2, G2, origins2, mapping):
                    continue
                counts['satisfying_joint_substitutions'] += 1
                if C.word != C2.word:
                    counts['changed_reference_substitutions'] += 1
                if len(C.word) != len(C2.word):
                    counts['length_changing_substitutions'] += 1
                at = lambda v: v if v <= m else mapping[v]
                for A, s, t in queries:
                    assert query_path(G2, A, at(s), at(t)) is not None
                    counts['independent_rechecked_query_atoms'] += 1
                if len(concrete_examples) < 6 and len(C.word) != len(C2.word):
                    concrete_examples.append({'base': B.word, 'old': C.word,
                         'new': C2.word, 'marks': list(zip(marks, chosen)),
                         'joint_atoms': len(queries)})
    assert counts['changed_reference_substitutions'] > 0
    assert counts['length_changing_substitutions'] > 0
    return {'status': 'PASS', 'seed': 2026091532,
            'counts': dict(sorted(counts.items())), 'examples': concrete_examples,
            'scope': 'Finite shared-diagram substitution checks, not the full symbolic compiler',
            'unrestricted_decider_executed': False,
            'independent_mathematical_review': False, 'lean_checked': False}


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output', type=Path, default=ROOT / 'results/query-grafting.json')
    args = p.parse_args()
    if not __debug__: p.error('Assertions must remain enabled')
    out = check(); text = json.dumps(out, indent=2, sort_keys=True) + '\n'
    args.output.write_text(text); print(text)
