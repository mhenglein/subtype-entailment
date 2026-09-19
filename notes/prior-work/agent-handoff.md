# Agent handoff: use the scholarship without inheriting false conclusions

## First ten minutes

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

## Scientific snapshot: what must not be rolled back by an old handoff

At the inspected base `df222241dc1a55ac6ee5da3cba3aedf662b3e285`, STATE already records `closure_reverse` for the executable diagram compiler. An earlier conversation described a weaker intermediate extension-existence theorem; that is not the current main endpoint. Do not tell a successor that the entire reverse implication is still missing merely because that older chat said so.

The same base still leaves forward coverage of the diagram enumeration, remaining clause-weight/finishing obligations, and the full semantic composition unresolved in Lean. The unwind results explicitly assume `ClosureFor`. Arbitrary-tree semantics and executable normalized satisfiability are not an unbounded entailment decision. C080 remains a candidate, with independent human review requested in #33. Later main may improve this state; follow the actual declarations and ledger rather than freezing this document as authority.

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
Reproduction, independent review and checked revision:
```

For C080-style graph surgery, split four tasks: reconstruct one common extension; transport every atom on that extension; prove all valid extensions are covered; bound the effective repeated construction. A finite list of syntactically legal diagrams addresses none of these automatically. Preserve literal edge directions, physical interval identity, marks, state colors, empty paths and overlap cases.

For an undecidability route, identify the missing terminal-anchor gadget and the direction of every reduction. An auxiliary automaton hardness result does not settle subtype entailment without a reverse realization. For a decidability route, give a computable cover or termination proof, not only an effective test for each proposed certificate.

## Where to spend effort next

Choose one [open obligation](open-obligations.md), post a scoped issue claim, and define a falsifiable deliverable. Particularly valuable are an independent reading of the thesis counterexample, an actual Schubert Lemma 5.5 counterexample, or a precise imported-theorem mapping. A broad survey alone should not be presented as a discharged proof obligation.

Keep both constructive and adversarial directions live. A useful negative result states exactly which stronger shortcut it refutes and whether a weaker existential replacement remains possible. Save the input, hypothesis and direct predicate, not only a failing optimized implementation.

## Publication and evidence rules

This documentation pass does not alter C/Q/A/E status, prove a new global theorem, or claim human review. A source marked RECORD or LEAD must not later become a proof dependency solely by being copied into another note. Record changes in inspection depth explicitly. Reuse existing source keys rather than counting preprint, proceedings and journal versions as independent discoveries.

At handoff, publish the exact commit, changed paths, validation outcomes and remaining obligations; release the owned paths. Other sessions' unpushed work is not visible through GitHub and must not be described as saved or clean without their checkpoint reports.
