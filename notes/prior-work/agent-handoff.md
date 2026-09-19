# Agent handoff: use the scholarship without inheriting false conclusions

## Current authority and the dated review

Read current [STATE](../../STATE.md), [PLAN](../../research/PLAN.md), and issues
[#34](https://github.com/mhenglein/subtail/issues/34) and
[#37](https://github.com/mhenglein/subtail/issues/37) for scientific status,
owner instructions and reservations. This file does not pause or resume work.
The [September 19 review](review-2026-09-19.md) gives a commit-pinned relevance
map; it must not override later canonical records.

The earlier scholarship handoff was published while proof work was paused.
That was historical context at `5e156fc`, not a current pause instruction.
The owner-selected acceptance path recorded by the project is kernel checking
plus nonauthor statement readback; no external human referee is commissioned.
Verify current instructions before relying on that operational snapshot too.

## First ten minutes on an authorized resumption

Read current [AGENTS](../../AGENTS.md), [problem](../../research/problem.md), [STATE](../../STATE.md), [claims](../../research/claims.md), and the relevant [approach history](../../research/approaches/). Search issue #36 for literature ownership and #37 for integration ownership; proof coordination remains in #34 and its children. Do not take an old timestamp as release of another worker's scope.

Then read [failure modes](failure-modes.md) before choosing an algorithm, pumping argument, finite quotient, or undecidability encoding. Resolve a cited source through [bibliography](bibliography.md) and [sources.json](sources.json), not an old chat summary.

Useful repository commands:

```sh
python3 scripts/research_index.py --lookup C080
python3 scripts/research_index.py --lookup Q004
python3 notes/prior-work/check_scholarship.py
python3 scripts/research_index.py --check
```

These commands retrieve/check records. They do not by themselves prove C080 or certify a paper's novelty.

## Use current declarations, not historical task lists

The original scholarship pass at `df22224` and `5e156fc` preceded later
coverage, terminal decision and summary/safe-split integration. Its old lists
of missing implications are historical. Retrieve C080, C029 and C031, then
follow current STATE and exact declaration readbacks. A checked subclaim does
not establish every stronger bound or the final subtype theorem.

Bounded cross-corpus retrieval from the repository root:

```sh
python3 notes/prior-work/search.py --search "finite quotient" --limit 8
python3 notes/prior-work/search.py --search "infinite continuation" --limit 12
python3 notes/prior-work/search.py --lookup F13
python3 notes/prior-work/search.py --lookup PW-SCH21
python3 notes/prior-work/search.py --lookup O11
python3 notes/prior-work/search.py --lookup C029
```

The tool reads the existing records, reports truncation and returns related
IDs. It does not validate mathematics or search external literature. A zero
hit count means no lexical/topic match in this local corpus.

## The useful mathematical interface

A safe import record should have this shape:

```text
Source key, version and exact theorem/page:
Source input, signature, tree/word domain, epsilon conventions:
Quantifiers and shared variables:
Effective representation and complexity measure:
Our input -> source input mapping:
Forward implication:
Reverse implication (or why not needed):
Conclusion actually obtained:
Unproved transfer/coverage/termination obligations:
Reproduction, independent readback and checked revision:
```

For C080-style graph surgery, split four tasks: reconstruct one common extension; transport every atom on that extension; prove all valid extensions are covered; bound the effective repeated construction. A finite list of syntactically legal diagrams addresses none of these automatically. Preserve literal edge directions, physical interval identity, marks, state colors, empty paths and overlap cases.

For an undecidability route, identify the missing terminal-anchor gadget and the direction of every reduction. An auxiliary automaton hardness result does not settle subtype entailment without a reverse realization. For a decidability route, give a computable cover or termination proof, not only an effective test for each proposed certificate.

## Choose a task within current authorization

Choose one [open obligation](open-obligations.md), use its [task contract](agent-tasks.md), post a scoped issue claim, and define a falsifiable deliverable. Particularly valuable are a non-author reading of the thesis counterexample, an actual Schubert Lemma 5.5 counterexample, or a precise imported-theorem mapping. A broad survey alone should not be presented as a discharged proof obligation.

Keep both constructive and adversarial directions available. A useful negative result states exactly which stronger shortcut it refutes and whether a weaker existential replacement remains possible. Save the input, hypothesis and direct predicate, not only a failing optimized implementation.

## Publication and evidence rules

This documentation pass does not alter C/Q/A/E status, prove a new global theorem, or claim human review. A source marked RECORD or LEAD must not later become a proof dependency solely by being copied into another note. Record changes in inspection depth explicitly. Reuse existing source keys rather than counting preprint, proceedings and journal versions as independent discoveries.

At handoff, publish the exact commit, changed paths, validation outcomes and remaining obligations; release the owned paths. Other sessions' unpushed work is not visible through GitHub and must not be described as saved or clean without their checkpoint reports.
