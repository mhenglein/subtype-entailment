"""Idempotent, additive integration of the recovered September 8 research.

Only the named shared metadata files are changed. Existing approach owners,
statuses, next steps, scientific claims, and unrelated evidence are retained.
This script neither commits nor pushes. Run the normal index checks afterward.
"""
import argparse
import json
from pathlib import Path

TAG = 'saved-research-recovery-2026-09-09'
RECORD = 'research/SAVED_RESEARCH_RECOVERY.md'
EVIDENCE = [
    RECORD, 'research/FLAG_TRANSPORT.md', 'research/COLLECTIVE_GAP_INFERENCE.md',
    'notes/2026-09-08-flag-transport-and-separator-obstruction.md',
    'notes/2026-09-08-collective-and-cross-gap-transport.md',
    'experiments/flag_transport.py', 'experiments/separator_tail.py',
    'experiments/check_flag_transport.py', 'experiments/collective_transport.py',
    'experiments/gap_equivalence.py', 'experiments/power_transport.py',
    'experiments/calculus_limits.py', 'experiments/search_calculus.py',
    'experiments/check_collective_research.py',
    'results/flag-transport.json', 'results/collective-gap-research.json',
]


def integrate(root):
    if not (root / 'AGENTS.md').is_file():
        raise ValueError('Expected the Subtail repository root')
    for path in EVIDENCE:
        if not (root / path).is_file():
            raise ValueError('Missing recovery evidence: ' + path)
    writes = {}
    state_path = root / 'STATE.md'
    state = state_path.read_text()
    if TAG not in state:
        lines = state.splitlines(keepends=True)
        if not lines or not lines[0].startswith('# Subtail'):
            raise ValueError('Unexpected STATE heading; preserve the file for review')
        addition = (
            '\n## September 9 recovery: flag rewrites and cross-gap inference\n\n'
            '<!-- ' + TAG + ' -->\n'
            'The two previously local research bundles are now repository-contained: '
            'source, proofs, counterexamples, and reproducible results. '
            'Exact gap-implication backends compute the greatest gap-equivalent '
            'annotation on a fixed terminal automaton. Guarded cyclic predecessor '
            'proofs and periodic-grid cross-gap rules preserve witnesshood; they '
            'close the recorded six-state barrier and seven-state equality-cycle '
            'examples. A terminating flag calculus is NOT a complete existence '
            'procedure; its preserved counterexamples still require other methods.\n\n'
            '[Recovery, commands, and scope](' + RECORD + '). '
            'Written proofs remain pending independent mathematical review; '
            'no new Lean proof or unrestricted decision is claimed. '
            'The earlier and concurrent work below is retained unchanged.\n\n'
        )
        writes[state_path] = lines[0] + addition + ''.join(lines[1:])
    for aid in ('A012', 'A017'):
        path = root / 'research' / 'approaches' / (aid + '.md')
        text = path.read_text()
        if TAG not in text:
            writes[path] = text.rstrip() + (
                '\n\n### 2026-09-09 — Recover checked local flag-inference work\n\n'
                '<!-- ' + TAG + ' -->\n'
                'Author: ChatGPT. Integration base: '
                '`917ced2d49c3c7173368d99bf134bf7cc1212f42`. '
                'The September 8 flag-transport and collective/cross-gap bundles '
                'were replayed from fresh extraction before publication. '
                'Their source/proof bytes and canonical result hashes are preserved. '
                'This is recovery/integration, not a new proof-status promotion.\n\n'
                '[Recovery record](../SAVED_RESEARCH_RECOVERY.md), '
                '[transport scope](../FLAG_TRANSPORT.md), '
                '[gap and cross-gap scope](../COLLECTIVE_GAP_INFERENCE.md). '
                'Both all-length obstruction families and failed completeness '
                'strengthenings are retained. Exact finite normalization does not '
                'supply unrestricted completeness. Existing owners, execution '
                'statuses, next steps, and prior history remain unchanged.\n'
            )
    index = root / 'experiments' / 'README.md'
    text = index.read_text()
    if TAG not in text:
        writes[index] = text.rstrip() + (
            '\n\n## Recovered flag-inference experiments\n\n'
            '<!-- ' + TAG + ' -->\n'
            'The two September 8 scoped attempts allocate no new global IDs. '
            '[Recovery and integrity manifest](../research/SAVED_RESEARCH_RECOVERY.md) '
            'links their exact seeds, finite coverage, written proofs, and limits.\n\n'
            'Run `python3 scripts/check_recovered_research.py --replay` to rerun '
            'both new checkers, the unchanged core checker, and the previous '
            'last-flag checker. This verifies 17 source/proof files and the '
            'canonical hashes of both saved result objects. Stored results are '
            'compact JSON; canonical pretty-printing recovers the original blobs.\n'
        )
    path = root / 'research' / 'approaches.json'
    registry = json.loads(path.read_text())
    changed = False
    targets = {row['id']: row for row in registry['approaches'] if row['id'] in ('A012', 'A017')}
    if len(targets) != 2:
        raise ValueError('Expected unique A012 and A017 records')
    for row in targets.values():
        for evidence in EVIDENCE:
            if evidence not in row['evidence']:
                row['evidence'].append(evidence)
                changed = True
    if changed:
        writes[path] = json.dumps(registry, indent=2, ensure_ascii=False) + '\n'
    # All inputs are checked before the first metadata write.
    for path, text in writes.items():
        path.write_text(text, encoding='utf-8')
    return [str(path.relative_to(root)) for path in writes]


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parents[1])
    args = parser.parse_args()
    print(json.dumps({'updated': integrate(args.root.resolve())}, sort_keys=True))
