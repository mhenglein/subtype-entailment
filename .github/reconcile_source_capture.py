"""Reconcile source-capture research with concurrent main; temporary helper."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import zlib

BASE = '00b09066e4ca620f91a308cf55c77b7720c28882'
raw = zlib.decompress(b''.join((Path('.github/source_capture_payload') / str(i)).read_bytes() for i in range(4)))
assert hashlib.sha256(raw).hexdigest() == 'b79a1e85e0bf501734987d960fef12a845faa0b9d4ca888092a5e61a6dbd34d8'
bundle = json.loads(raw)
new_paths = {'experiments/source_capture.py', 'experiments/check_source_capture.py', 'notes/2026-09-09-source-capture-word-equations.md', 'research/conjectures/Q004.md', 'results/source-capture.json', 'results/source-capture-smt.json'}
assert set(bundle) == new_paths | {'integrate_records.py'}
# Rename only unpublished source-capture records, never concurrent main's IDs.
for path in ('integrate_records.py', 'research/conjectures/Q004.md'):
    for old, new in (('C065','C067'), ('C066','C068'), ('E042','E043'), ('c065','c067'), ('c066','c068'), ('e042','e043')):
        bundle[path] = bundle[path].replace(old, new)
helper = bundle['integrate_records.py'].replace("BASE = '05b20ee73841d0e7105a44beb761e553a7081a8d'", "BASE = '" + BASE + "'")
# Do not touch unrelated A018 wording when reconciling the scientific result.
helper = '\n'.join(line for line in helper.splitlines() if not line.startswith("change('STATE.md','- A018")) + '\n'
temporary = Path(os.environ['RUNNER_TEMP']) / 'source_capture_bundle'
temporary.mkdir(parents=True, exist_ok=True)
(temporary / 'integrate_records.py').write_text(helper)
for path in new_paths:
    saved = temporary / path
    saved.parent.mkdir(parents=True, exist_ok=True)
    saved.write_text(bundle[path], encoding='utf-8')
subprocess.run(['git','checkout','--detach',BASE], check=True)
assert not subprocess.check_output(['git','status','--porcelain'],text=True).strip()
original = json.loads(Path('research/approaches.json').read_text())
for relative in new_paths:
    target = Path(relative)
    assert not target.exists(), relative
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text(bundle[relative], encoding='utf-8')
subprocess.run(['python3',str(temporary / 'integrate_records.py')], check=True)
# Workflow updates are published separately by the authorized connector.
subprocess.run(['git','restore','--source='+BASE,'--','.github/workflows/checks.yml'],check=True)

next_steps = {
'A017': 'Independently audit C067/C068, then attack Q004: a computable existential source-visit bound or complete shared-word cover for recurrent sources. Retain the concurrent guarded-order cover route and its terminal-anchor boundary; single-source root pumping is no longer needed for decidability.',
'A011': 'Use C067/C068 to constrain negative encodings: single-source and effectively bounded-source outputs are decidable. Continue the concurrent two-counter investigation at its exact terminal-anchor/trailing-context gap; no unrestricted reduction is established.',
'A012': 'Use C067 for exact source-local impossibility/pruning without assuming local YES answers compose (C042). Combine bounded-source word equations and the guarded-order backend in a proposed complete shared-word NO cover; separate soundness, coverage and termination.',
'A008': 'Test minimum flagged-source visits for Q004 using the two-source new-border regression. Cross-check C067 against the concurrent C065 one-flag counting procedure on their overlap; retain quantitative counting bounds and guarded-order regressions as separate contributions.'}
data = json.loads(Path('research/approaches.json').read_text())
old_rows = {row['id']: row for row in original['approaches']}
for row in data['approaches']:
    before = old_rows[row['id']]
    for field in ('owner','status','outcome'):
        assert row[field] == before[field], (row['id'],field)
    if row['id'] in next_steps:
        row['next_step'] = next_steps[row['id']]
        record = Path(row['record'])
        record.write_text(record.read_text().rstrip() + '\n\n**Concurrent integration.** Reconciled onto `' + BASE + '`. The one-flag counting and guarded-order records, evidence and histories are retained. Source-capture claims use C067/C068 and E043 because concurrent main already assigned C065/C066/E042. Current combined next step: ' + row['next_step'] + '\n')
    if row['id'] == 'A017':
        row['summary'] += ' Concurrent guarded-order chains have their own complete restricted solver; an arbitrary recurrent cover and terminal-anchor reduction remain open.'
    assert set(before['evidence']) <= set(row['evidence']), row['id']
Path('research/approaches.json').write_text(json.dumps(data,indent=2,ensure_ascii=False)+'\n')
proof = Path('notes/2026-09-09-source-capture-word-equations.md')
proof.write_text(proof.read_text().rstrip() + '\n\n## Concurrent integration and claim identity\n\nThis argument was developed from `05b20ee` and integrated onto concurrent main\n`' + BASE + '`. Its canonical IDs are C067/C068 and E043.\nConcurrent C065 supplies a different one-flag counting decision with an explicit\nwitness-length bound; C066 refutes naive two-target incidence subtraction.\nThe source-capture formula treats all targets on the same word and therefore\ndoes not use that subtraction. It does not supply the counting method\'s explicit\nbound. The guarded-order solver and its terminal-anchor obstruction are also\nretained; no independent re-certification of those proofs is claimed here.\nSee [one-flag counting](../research/ONE_FLAG_COUNTING.md) and\n[the parallel order-cover route](../research/ORDER_COVER_ROUTE.md).\n')
counting = Path('research/ONE_FLAG_COUNTING.md')
counting.write_text(counting.read_text().rstrip() + '\n\n## Concurrent continuation: arbitrary single-source target sets\n\nC067 gives a different written decision/PSPACE upper-bound argument for all\nsingle-source terminal target sets, using prefix-free capture and shared-word\nequations; C068 handles supplied source-visit sequences. Independent review\nis pending. This bypasses the joint-counting extension for decidability, not\nfor explicit counting series or the quantitative bounds recorded above. C065\nand the C066 subtraction counterexample are preserved unchanged.\n[Proof, compiler and exact limits](../notes/2026-09-09-source-capture-word-equations.md).\n')
subprocess.run(['python3','scripts/research_index.py'],check=True)
print('Reconciled source-capture research; concurrent files and evidence retained.')
