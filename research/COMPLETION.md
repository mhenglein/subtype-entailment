# Completion checklist

Updated: 2026-09-21. Owner: Marcus. Completion tracker: [#63](https://github.com/mhenglein/subtail/issues/63).
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
- **C087 / #70:** ordinary logspace PSPACE hardness for arbitrary and regular
  bottom/product entailment, independently reviewed; no finite-tree transfer.
- **C088 / #71:** ordinary arbitrary-tree decision with explicit top by at most
  four C081 calls; language lifting/decomposition checked in Lean. The full
  expression compiler and native top interface remain separate work.
- **C030 core:** checked satisfiability and same-word realization on `2k+1`
  variables under terminal-finality. Budget preservation remains an ordinary
  proof and reproduction result, with a separate formalization issue below.
- **Useful prototype:** checked optimizations, JSON interface, complete ordinary
  countermodel extraction and Lean checking of supplied arbitrary-tree graph
  certificates. E060 completes 38/38 fixed and 19/19 deeper cases; the six-variable
  empty raw stress input remains UNKNOWN under its 20-second cap.
- **C089–C091:** reviewed ordinary fixed-positive-arity reduction, graph-only
  first-return preimage theorem, and function-only characterization/nonadditivity
  obstruction. These are separate companion results with bounded component checks.
- **Paper/artifact draft:** full ordinary terminal and finite-tree arguments,
  Henglein–Rehof/ Niehren–Priesnitz comparison, declaration map and research tag.

These statements retain their exact hypotheses and evidence levels. They do
not assert publication priority, a tight complexity class, practical completion
on every input, a complete formal explicit-top implementation, or other signatures.

## Finish the paper and reproducible release

| Order | Remaining deliverable | Acceptance | Issue |
|---|---|---|---|
| 1 | Frozen-paper mathematical and contribution review | Whole-manuscript readback, exact contribution/source domains, declaration map and rendered PDF; outcome at the current candidate receipt | [#79](https://github.com/mhenglein/subtail/issues/79); earlier [#64](https://github.com/mhenglein/subtail/issues/64) preserved |
| 2 | Reproducible release | Clean-environment proof/CLI/experiment receipt; accurate documentation; finalized metadata and immutable release checkpoint | [#65](https://github.com/mhenglein/subtail/issues/65) |

The proof milestone is complete. A paper/artifact release is done when both
rows are complete at one recorded revision. The release can state the current
performance limits and Python trust boundary without claiming stronger results.
Marcus has explicitly deferred licensing and requested author/affiliation
placeholders. Work on reproducibility can proceed; final metadata and a licensed
public release wait for those choices. Do not ask again merely to clean up issues.
No external human referee is automatically commissioned.

Earlier September 20 technical checkpoint: the [manuscript acceptance record](../notes/2026-09-20-publication-acceptance.md)
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
| Complexity | Tighten the upper bound/classification after C087 PSPACE hardness | Explicit encoding, tree domain and resource accounting; prove every literature transfer | [#70](https://github.com/mhenglein/subtail/issues/70) |
| Completed new signature | Explicit top: C088 ordinary decision and checked language core | Full ordinary theorem reviewed and integrated; complete expression-level formalization and solver exposure are separate follow-up proposals | [#71](https://github.com/mhenglein/subtail/issues/71) |
| Other consequences | Arity, constructor labels, variance and automata results | One exact reviewed transfer/result at a time; separate semantic obligations | [#72](https://github.com/mhenglein/subtail/issues/72) |
| Optional converse certification | Formal C030 budget preservation | Connect the exact ordinary budget statement to checked declarations and differential evidence | [#73](https://github.com/mhenglein/subtail/issues/73) |

Current bounded dispositions: #66 diagnostics, C089 fixed arity, C090 graph-only
preimages, C091 variance analysis and #67 native diagnostics are integrated in
the [publication candidate](../notes/2026-09-21-publication-candidate.md).
Their broader issues remain open for the exact questions above. The native
suite distinguishes strict answers, inspections, frontend shortcuts and capped
stress; none is substituted for automatic depth-two terminal coverage. #68's
reviewed producer is explicitly deferred pending its promised author handoff.
Its branch is preserved, with a public coordination request. New implementation
requires a fresh scoped claim; no worker is assigned here.

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

## Hardness/top integration checkpoint

[Integration record](../notes/2026-09-20-hardness-top-integration.md) pins the
new paper, source-preserving merges and combined proof/corpus checks. #70 remains
open for the exact complexity frontier. #71's stated ordinary theorem and
selective-formalization acceptance are complete. A future implementation should
formalize the labelled-tree correspondence and finite projection compiler,
compose the four C081 calls, then add explicit-top syntax and countermodel
output. No worker or file is reserved for that follow-up. The later publication candidate integrates the released arity, automata,
variance and native diagnostic submissions. The reviewed producer remains
deferred pending handoff. See the current disposition above.


## Current technical publication checkpoint

The [September 21 record](../notes/2026-09-21-publication-candidate.md) separates
whole-paper agent review, primary-source comparison, visual inspection and fresh
Linux reproduction. Its receipt is the authority for actual checked revisions
and outcomes. The release runner now includes the optional quantitative/top
modules and newly accepted corpora and rejects stale PDF provenance or missing
case coverage. This completes only the technical gates once the receipt passes.
License, authors/affiliations and a final public release remain explicitly
deferred. No external human referee, venue or cloud service is required or
commissioned by repository cleanup.
