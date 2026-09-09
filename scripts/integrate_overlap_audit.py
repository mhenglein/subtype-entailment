"""Add the checked overlap-deletion audit to shared records without Git writes."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TAG = 'overlap-deletion-audit-2026-09-09'
NOTE = 'notes/2026-09-09-overlap-deletion-audit.md'
EVIDENCE = [NOTE, 'experiments/overlap_deletion.py',
            'experiments/check_overlap_deletion.py', 'results/overlap-deletion-audit.json']


def integrate(root):
    for path in EVIDENCE:
        if not (root / path).is_file():
            raise ValueError('Missing audit evidence: ' + path)
    writes = {}
    state_path = root / 'STATE.md'
    state = state_path.read_text()
    if TAG not in state:
        title, rest = state.split('\n', 1)
        writes[state_path] = title + (
            '\n\n## September 9 audit: overlapping deletions need full alignment closure\n\n'
            '<!-- ' + TAG + ' -->\n'
            'The equality-preservation clause of the paired-overlap pumping '
            'lemma is false for overlapping occurrences, including its stated '
            'large-shift window. A six-state family preserves acceptance after '
            'the two loop deletions but destroys the selected factor equality. '
            'The original note now carries a visible correction.\n\n'
            'A corrected deletion-mask closure computes all physical positions '
            'that must be removed consistently across the supplied equalities. '
            'Loop and protected-cut checks give executable certificates for '
            'acceptance, those equalities, and their endpoint states. This repairs '
            'the local example, not the no-new-forbidden-border or global '
            'small-model obligation. [Proof, counterexample, and checks](' + NOTE + '). '
            'Written proof plus reproduction; independent review pending, not Lean.\n\n'
        ) + rest
    path = root / 'research/approaches/A017.md'
    text = path.read_text()
    if TAG not in text:
        writes[path] = text.rstrip() + (
            '\n\n### 2026-09-09 — Audit overlapping pair deletions and repair their mask invariant\n\n'
            '<!-- ' + TAG + ' -->\n'
            'Author: ChatGPT. Reviewed `917ced2`; continued after `653ab778`. '
            'The two-deletion equality clause fails even when both deletion '
            'intervals lie inside both overlapping occurrences and the shift '
            'exceeds the state-count square. All 666 collision choices in the '
            'recorded large-shift window fail. A minimal alignment-compatible '
            'mask and separate state-loop/cut checks repair the local surgery. '
            'No global witness bound follows; new borders remain unhandled.\n\n'
            '[Full proof and scope](../../' + NOTE + '), '
            '[checker](../../experiments/check_overlap_deletion.py), '
            '[saved evidence](../../results/overlap-deletion-audit.json). '
            'Seed 2026090901; 78 counterexample/repair cases, 364 exhaustive '
            'short mask-minimum queries, 5,616 surviving-factor checks, and '
            '500 multi-alignment comparisons. Independent mathematical review '
            'pending; not Lean-checked. Preserve the earlier note as a corrected '
            'historical attempt, not as an established overlap lemma.\n'
        )
    path = root / 'experiments/README.md'
    text = path.read_text()
    if TAG not in text:
        writes[path] = text.rstrip() + (
            '\n\n## Overlap-deletion audit\n\n<!-- ' + TAG + ' -->\n'
            'Run `python3 experiments/check_overlap_deletion.py`. '
            '[Scope and all-length arguments](../' + NOTE + ') distinguish '
            'selected equality/acceptance preservation from witness preservation. '
            '[Result](../results/overlap-deletion-audit.json), seed 2026090901. '
            'This scoped audit allocates no new global claim/experiment IDs.\n'
        )
    path = root / 'research/approaches.json'
    data = json.loads(path.read_text())
    rows = [row for row in data['approaches'] if row['id'] == 'A017']
    if len(rows) != 1:
        raise ValueError('Expected a unique A017 record')
    added = [e for e in EVIDENCE if e not in rows[0]['evidence']]
    if added:
        rows[0]['evidence'].extend(added)
        writes[path] = json.dumps(data, indent=2, ensure_ascii=False) + '\n'
    for path, text in writes.items():
        path.write_text(text, encoding='utf-8')
    return [str(p.relative_to(root)) for p in writes]


if __name__ == '__main__':
    print(json.dumps({'updated': integrate(ROOT)}, sort_keys=True))
