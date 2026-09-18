# Research tracker

Problem 1.7 is open. This is the current map of approaches, including unsuccessful work.

**16 tried · 1 not tried · 1 blocked · 0 active**

Read [the problem and notation](problem.md), [claims and evidence](claims.md), and [the experiment index](../experiments/README.md).

Use [the research plan](PLAN.md) for the eleven proposed angles, priorities, and dependencies, including the Lean workstream.

Choose a record below to see its scope, attempt history, evidence, and limitations. All unowned work is available to discuss; nobody has been assigned automatically.

## How to read the status

- **Not tried:** a proposed approach; reading a related paper does not count as trying it.
- **Active:** someone is currently working on it and is named as owner.
- **Blocked:** a specific dependency prevents the next step; the record says whether any prior attempt exists.
- **Tried:** an attempt and evidence are recorded. This does not mean the problem is solved.

Outcomes are separate: **supported** applies to the stated limited claim, **refuted** to the exact failed claim, **inconclusive** to an attempt without a verdict, and **open** to unresolved work. Proof status is recorded in the claims ledger.

## Active work

None currently.

## Not tried

| ID | Approach | Finding / next step | Owner |
|---|---|---|---|
| A014 | [Apply cap and period-language saturation techniques](approaches/A014.md) | Choose one closure property, test small instances, and preserve all endpoint flags. | Unassigned |

## Blocked

| ID | Approach | Finding / next step | Owner |
|---|---|---|---|
| A007 | [Reproduce the original memo's code and census](approaches/A007.md) · [#1](https://github.com/mhenglein/subtail/issues/1) | The original analysis-2026 folder has not been supplied. Next: Import original sources unchanged, record provenance, and cross-check against the independent implementation. | Unassigned |

## Tried: results and dead ends

| ID | Approach | Finding / next step | Owner |
|---|---|---|---|
| A001 | [Audit the top-free characterization](approaches/A001.md) | Supported: Theorem 2.6 supports canonical regular countermodels under its satisfiability premise. Next: No new work assigned; use the audited statement as a dependency. | Unassigned |
| A002 | [Replace prefix reachability with a regular language](approaches/A002.md) | Refuted: The old formula disagrees on 4,017 words through length 11; the all-length family is nonregular. Next: Do not reuse the old formula; retain the corrected cap decomposition. | Unassigned |
| A003 | [Bound all rigid witnesses using nonmerging runs](approaches/A003.md) | Refuted: Two states admit rigid words 0^n with unbounded repeated suffixes, while the runs merge. Next: Use minimal witnesses and stronger cuts instead. | Unassigned |
| A004 | [Transfer the shorter word's repeated suffix](approaches/A004.md) | Supported: C008 has a written proof and a checked binary Lean proof; earlier bounded cuts also pass. Next: Use C008 and the stronger C013 context rule in A008. | Unassigned |
| A005 | [Weaken state equality to incoming flag-set inclusion](approaches/A005.md) | Supported: C009 has a written proof and a checked binary Lean proof with the incoming-flag direction verified. Next: Compare witnesses resistant to C009 and C013 in A008. | Unassigned |
| A006 | [Calibrate small-budget expectations](approaches/A006.md) | Refuted: A singleton 0^n language has exact B=n-1 at n+1 states; the checked 13-state instance has B=11. Next: Use this baseline before searching for harder growth in A009. | Unassigned |
| A008 | [Bound minimal witnesses after stronger truncation](approaches/A008.md) · [#2](https://github.com/mhenglein/subtail/issues/2) | Supported: Complete four-state terminal census: witness length at most four and budget at most two; general three-state proof remains separate. Next: Test minimum flagged-source visits for Q004 using the two-source new-border regression. Cross-check C067 against the concurrent C065 one-flag counting procedure on their overlap; retain quantitative counting bounds and guarded-order regressions as separate contributions. | Unassigned |
| A009 | [Find budget growth beyond the regular-language baseline](approaches/A009.md) | Supported: A one-flag k-state family has exact B=2k-4 and shortest length 3k-3; five states refute B<=\|K\|. Next: Any universal abstract bound must allow 2k-4. Separate abstract growth from actual summary outputs, which satisfy absorption. | Unassigned |
| A010 | [Build the exact top-free constraint-to-automata pipeline](approaches/A010.md) · [#3](https://github.com/mhenglein/subtail/issues/3) | Supported: Implemented actual W/Wrev summaries with S/F annotations; independent audit fixed two API errors and found no known comparison mismatch. Next: Generate actual subtype-derived instances and test joint summary invariants in A013. | Unassigned |
| A011 | [Complete the converse with regular annotations](approaches/A011.md) | Supported: Every k-state terminal-final binary abstract instance has an exact word-preserving subtype realization on 2k+1 variables. Next: Use C067/C068 to constrain negative encodings: single-source and effectively bounded-source outputs are decidable. Continue the concurrent two-counter investigation at its exact terminal-anchor/trailing-context gap; no unrestricted reduction is established. | Unassigned |
| A012 | [Make NO certificates complete](approaches/A012.md) · [#15](https://github.com/mhenglein/subtail/issues/15) | Inconclusive: A six-state nonflat NO language has an all-length arithmetic certificate and defeats every candidate-covering regular separator decoration with a finite semantic-tail bound. Next: Use C067 for exact source-local impossibility/pruning without assuming local YES answers compose (C042). Combine bounded-source word equations and the guarded-order backend in a proposed complete shared-word NO cover; separate soundness, coverage and termination. | Unassigned |
| A013 | [Exploit restrictions shared by actual summary automata](approaches/A013.md) | Supported: The terminal branch realizes arbitrary abstract flags; a nine-variable system has a nonregular terminal separating language. Flat terminal graphs are decidable arithmetically. Next: Target nonflat productive terminal components; shared B/A/D structure alone cannot exclude terminal abstract instances. | Unassigned |
| A015 | [Strengthen truncation using occurrence context](approaches/A015.md) | Supported: Proved three context refinements and formalized the binary visited-state rule; strict examples and exhaustive two-state checks pass. Next: Use the visited-state summary to classify shortest witnesses resisting every admissible cut in A008. | Unassigned |
| A016 | [Implement and audit fixed-skeleton checkability](approaches/A016.md) | Supported: Implemented exact Presburger skeleton formulas and a finite complete cover for flat terminal graphs; unbounded loop counts are retained. Next: Use the exact supplied-skeleton solver to test finite-cover hypotheses for nonflat terminal inputs. Audit any critical arithmetic transfer; add Lean formalization only for a specific uncertainty or stable dependency. A supplied-schema solver is not a complete cover, and caps remain UNKNOWN. | Unassigned |
| A017 | [Bound essential repeated blocks](approaches/A017.md) · [#34](https://github.com/mhenglein/subtail/issues/34) | Inconclusive: A candidate complete ordinary proof (C080) reduces terminal witness existence to finite rank-query preimages over first-return prefix graphs and derives an explicit computable witness bound F(k). Two separate AI-assisted audits found no gap in its stages 1-5 or in the C029/C031 bridge; no human referee; Lean covers stages 1-2 only. Earlier finite reference quotients are refuted and retained. Problem 1.7's status is unchanged. Next: Obtain independent human review of the stage-4 promotion-preimage lemma (notes/2026-09-18-closure-lemma-referee-brief.md); build adversarial joint-conjunction and shared-generator fixtures against experiments/rank_preimage.py; keep Q004 and the opposing undecidability route as fallbacks if stage 4 fails. | Unassigned |
| A018 | [Maintain the Lean core and verify critical obligations](approaches/A018.md) · [#34](https://github.com/mhenglein/subtail/issues/34) | Supported: Lean kernel-checks the rank-query candidate's stages 1-2 (terminal border depth at most k-1, milestone first returns, failure-target confinement); stage 3 (coloured first-return graph surgery) is under active formalization on branch lean/first-return-graph-2026-09-18; stage 4a pins the query grammar, literal prefix-graph semantics, a kernel-checked decision of query satisfaction and the Closure Lemma as an unproved Prop; stages 4b-6 are unformalized. Next: Finish and integrate stage 3; instantiate the pinned ClosureFor with an executable preimage compiler and prove both directions (issues #28/#29); formalize the weight bound/unwind and the C029/C031 bridge as separate obligations. One GitHub issue per obligation under the milestone 'Rank-query closure formalized'. | Unassigned |

## Shared hypotheses

These records keep exact hypotheses and failed strengthenings together. Their stated status is not inferred from tests or activity.

| ID | Hypothesis | Recorded status |
|---|---|---|
| Q001 | [Q001 — Bounded essential terminal skeletons](conjectures/Q001.md) | OPEN |
| Q002 | [Q002 — Agreement-profile domination for terminal words](conjectures/Q002.md) | REFUTED |
| Q003 | [Q003 — Strict agreement-profile descent](conjectures/Q003.md) | REFUTED |
| Q004 | [Q004 — Computably bounded flagged-source visits](conjectures/Q004.md) | OPEN |

Retrieve one canonical record as JSON with `python3 scripts/research_index.py --lookup Q003` (also accepts A/C/E IDs). Follow its linked evidence before relying on it.

## Updating the record

1. Add a dated attempt to the approach's Markdown record; preserve previous failed and inconclusive attempts.
2. Update its status, outcome, owner, evidence links, and next step in [approaches.json](approaches.json).
3. Update the claims ledger or experiment index if a result changed.
4. Run `python3 scripts/research_index.py` from the repository root, complete the relevant checks, then commit and push authorized updates to `main`. Use a pull request only when requested.

Use [the contribution guide](../CONTRIBUTING.md). GitHub issues hold discussion; this registry holds the current research status. Closing an issue does not establish a theorem.

<!-- Generated by scripts/research_index.py. Edit approaches.json and approach records, then regenerate. -->
