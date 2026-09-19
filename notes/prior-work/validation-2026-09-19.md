# Structured literature review: validation and handoff

Session: `structured-literature-review-20260919`. Base:
`064fc7306b679bf607b91e7d8de259823f200c62`. Scope: `notes/prior-work/**`.
No scientific ledger, Lean module, experiment result, workflow or toolchain is
changed. No main integration lease is held. This is a documentation/retrieval
contribution prepared for review.

## What was reviewed

The core worker inspected historical subtype sources and failed-proof passages.
The adjacent worker inspected word-equation, border, containment, backreference
and graph-query statements. The parent inspected periodic/FDFA sources and
cross-checked critical adjacent statements, including DGH Section 4/Theorem 4,
BFR Theorem 6/Proposition 12, HHL Theorems 28–29 and KU Theorems 6–8.
Workers inherited the project dossier. This was not blind replication of a
whole proof, an external human review, or an end-to-end theorem audit.

Draft review required clarification of the distinction between a letter
involution and word reversal, removal of a noncanonical proposed witness
predicate, precise wording of the BFR finite-minimal-language test, and
alignment with current checked semantic/compiler progress. Only corrected
versions belong in the final contribution.

## Reproduction commands

Run at the repository root using Python 3:

```sh
python3 notes/prior-work/check_scholarship.py
python3 notes/prior-work/search.py --check
python3 notes/prior-work/test_search.py
python3 scripts/research_index.py --check
python3 -m unittest discover -s scripts -p 'test_research_index.py'
git diff --check
```

Useful retrieval smoke checks:

```sh
python3 notes/prior-work/search.py --search "finite quotient" --limit 8
python3 notes/prior-work/search.py --search "infinite continuation" --limit 3
python3 notes/prior-work/search.py --lookup PW-SCH21
python3 notes/prior-work/search.py --lookup F13
python3 notes/prior-work/search.py --lookup O11
python3 notes/prior-work/search.py --lookup C029
```

The short infinite-continuation search must report truncation. The Schubert
lookup must preserve withdrawn publication status independently of selected
primary-text inspection. C029 must come from the canonical ledger rather than
a copied literature summary. Unknown IDs must fail explicitly.

## Outcomes

All six reproduction commands above passed locally on the combined contribution
on 2026-09-19, after the workers released their files:

| Check | Outcome |
|---|---|
| Scholarship links, metadata and finite fixtures | PASS: 26 sources, 115 local targets, both fixtures |
| Unified lookup references | PASS: 223 records, 9 topics |
| New retrieval tests | PASS: 9 tests |
| Canonical research index | PASS: 18 approaches, 152 A/C/E/Q records |
| Existing navigation regressions | PASS: 13 tests |
| Diff whitespace | PASS |

The adjacent-source worker separately reviewed the parent synthesis, periodic
dossier, entry points, task contracts and retrieval files. It found no concrete
source-level error in that scope, ran the nine retrieval tests, and identified
confusing old bibliography labels and missing dated review pointers. Those
metadata findings were fixed. Its missing-core-file check occurred during the
core worker's rewrite; the final combined-tree index check above passed. This
review did not independently certify the adjacent worker's own dossier.

The parent inspected all three final dossiers, cross-checked the named adjacent
source statements, NP03's version/domain map, Schubert's withdrawal, and BPR19's
restriction/return conditions. It corrected the HHL proposed falsification test
to compare shared assignments on a bounded domain, rather than assume the
single-atom solver accepts a conjunction. It also clarified KU's uniformity and
expression-dependent cost. The core worker reported source-derived summaries
under 200 words per source; its proof readback remains explicitly selective.

Current main was re-read as the baseline SHA above before publication. The
commit-pinned PR and coordination handoff identify the exact delivered revision
and remote check outcomes. No remote CI success is inferred from these local
checks.

## Limits

No Lean build, kernel replay, full experiment suite, source-paper theorem proof
certification, full citation database export or external author contact is
performed for this documentation change. Existing mathematical statuses remain
unchanged. No bibliography size or passing navigation test establishes novelty.
Only the owned isolated checkout is inspected for local changes; other workers'
unpushed branches/stashes are outside this preservation claim.
