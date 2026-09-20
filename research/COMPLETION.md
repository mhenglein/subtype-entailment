# Completion checklist

Updated: 2026-09-20. Owner: Marcus. Completion tracker: [#63](https://github.com/mhenglein/subtail/issues/63).
Integration and scope claims stay in [#37](https://github.com/mhenglein/subtail/issues/37).
This document maps remaining deliverables to issues; mathematical status remains
in [STATE](../STATE.md) and the [claim ledger](claims.md). Issue creation assigns
no worker, changes no workstream owner and reserves no path.

## What is already done

- **C081:** total executable entailment for finite expressions over bottom and
  one covariant binary product, valued in arbitrary possibly infinite trees.
- **C085:** a separate total executable decision for finite-tree entailment.
- **C082:** the corrected larger terminal witness bound; the old concrete C080
  U estimate remains refuted.
- **C086 / #69:** the smaller compiler satisfies the original U contract, and
  the original terminal F is checked, reviewed and integrated with continuing CI.
  [Exact proof scope and evidence](../notes/2026-09-20-original-bounds-integration.md).
- **C030 core:** checked satisfiability and same-word realization on `2k+1`
  variables under terminal-finality. Budget preservation remains an ordinary
  proof and reproduction result, with a separate formalization issue below.
- **Useful prototype:** checked optimizations, JSON interface, complete ordinary
  countermodel extraction and Lean checking of supplied arbitrary-tree graph
  certificates. E060 completes 38/38 fixed and 19/19 deeper cases; the six-variable
  empty raw stress input remains UNKNOWN under its 20-second cap.
- **Paper/artifact draft:** full ordinary terminal and finite-tree arguments,
  Henglein–Rehof/ Niehren–Priesnitz comparison, declaration map and research tag.

These statements retain their exact hypotheses and evidence levels. They do
not assert publication priority, a tight complexity class, practical completion
on every input or a theorem for top/other signatures.

## Finish the paper and reproducible release

| Order | Remaining deliverable | Acceptance | Issue |
|---|---|---|---|
| 1 | Final mathematical and contribution review — completed at the recorded checkpoint | Exact source/theorem/domain attribution, examples/maps and all 28 PDF pages checked; bounded independent review accepted | [#64](https://github.com/mhenglein/subtail/issues/64) |
| 2 | Reproducible release | Clean-environment proof/CLI/experiment receipt; accurate documentation; finalized metadata and immutable release checkpoint | [#65](https://github.com/mhenglein/subtail/issues/65) |

The proof milestone is complete. A paper/artifact release is done when both
rows are complete at one recorded revision. The release can state the current
performance limits and Python trust boundary without claiming stronger results.
Marcus has explicitly deferred licensing and requested author/affiliation
placeholders. Work on reproducibility can proceed; final metadata and a licensed
public release wait for those choices. Do not ask again merely to clean up issues.
No external human referee is automatically commissioned.

September 20 technical checkpoint: the [manuscript acceptance record](../notes/2026-09-20-publication-acceptance.md)
separates source/literature, mathematical and visual reviews. The
[fresh project-cache reproduction](../notes/2026-09-20-clean-reproduction.md)
passed 18 selected checks at its recorded revision, including the optional
modules and actual CLI boundaries. The technical part of #65 has evidence;
the metadata and final release checkpoint remain pending. Current issue
dispositions and contributor ownership are in [STATE](../STATE.md#active-work-and-file-ownership)
and the issue comments; this record grants no overlapping write scope.

## Continue the broader research programme

| Priority | Exact remaining question | Completion evidence | Issue |
|---|---|---|---|
| Next practical | Reduce six-variable raw summary cost | Profile first, prove refinement, retain existing regressions; target completion at unchanged caps | [#66](https://github.com/mhenglein/subtail/issues/66) |
| Next validation | Exercise terminal promotion and shared generators | Independently justified branch-covering fixtures; exact small exhaustion, capped stress marked UNKNOWN | [#67](https://github.com/mhenglein/subtail/issues/67) |
| Verification hardening | Check the complete countermodel producer | Executable construction and completeness proof; finite certificate boundary and JSON trust boundary stated | [#68](https://github.com/mhenglein/subtail/issues/68) |
| Complexity | Tighten exact-semantic upper/lower bounds | Explicit encoding, tree domain and resource accounting; prove every literature transfer | [#70](https://github.com/mhenglein/subtail/issues/70) |
| New signature | Explicit top | Complete reviewed theorem for a precise extension, decision or undecidability; a study alone is insufficient | [#71](https://github.com/mhenglein/subtail/issues/71) |
| Other consequences | Arity, constructor labels, variance and automata results | One exact reviewed transfer/result at a time; separate semantic obligations | [#72](https://github.com/mhenglein/subtail/issues/72) |
| Optional converse certification | Formal C030 budget preservation | Connect the exact ordinary budget statement to checked declarations and differential evidence | [#73](https://github.com/mhenglein/subtail/issues/73) |

Current practical evidence: #66's separate native diagnostic identifies transition
construction and dense flag construction as capped phases; its n=6 complete
answer is still UNKNOWN. [E061](../experiments/README.md#e061) closes the scoped
independent Python fixture/review/replay portion of #67. Automatic successful
native depth-two and original-expression coverage remain open; six stress
calls stay UNKNOWN. The new #67 native follow-up has its own scope. The
[submission review](../notes/2026-09-20-submission-review.md) accepted the scoped
producer, hardness and extension contributions; their integration remains
separate from the completed compiler/F integration. Read the current ownership
record in [STATE](../STATE.md#active-work-and-file-ownership).

These issues preserve the wider requested programme. They are separate from
release gates and from the completed proof of Problem 1.7. A restricted result
must not close an unresolved general extension; a failed encoding refutes only
that encoding. An independent negative result is progress when its exact target
is stated. Resolve or explicitly defer each chosen programme target before
calling that larger programme complete.

## Retired trackers and preserved contributions

| Old item | Disposition | Remaining scope |
|---|---|---|
| #23 semantic bridge review | Completed by integrated bridge contracts and final C081 readback | Final manuscript acceptance in [#64](https://github.com/mhenglein/subtail/issues/64) |
| #28 forward closure | Checked and integrated | New stress coverage in [#67](https://github.com/mhenglein/subtail/issues/67), no reopened proof gap |
| #32 adversarial fixtures | Superseded after partial bounded coverage; preserve caps and original results | Uncompleted multi-atom/stress scope in [#67](https://github.com/mhenglein/subtail/issues/67) |
| #33 cross-session readback | Completed for C081; later C082 review recorded separately | Final manuscript/contribution acceptance in [#64](https://github.com/mhenglein/subtail/issues/64) |
| #30 and #34 quantitative stage trackers | Superseded by C081/C082/C086 | Original F/smaller-compiler obligations completed in #69; practical and tight complexity remain separate |
| PRs #44/#45 | Historical semantic and normalization advisories retained with current-status notices | No new proof claim from merging prose |
| PR #47 | Original counterexample, checker and replacement proof retained; C082 and C086 are distinct later results | No surviving original-F/smaller-compiler obligation; no practical runtime claim |
| PR #51 | Independent C030 source readback, fresh combined-tree validation and continued CI coverage | [#73](https://github.com/mhenglein/subtail/issues/73) |

[Reconciliation evidence and exact source heads](../notes/2026-09-20-repository-reconciliation.md).
The standing coordination issue #37 remains open for future leases; it is not
an unfinished mathematical task. Historical branches/worktrees are retained.
Unowned local changes, stashes and unpushed work were not audited or deleted.
