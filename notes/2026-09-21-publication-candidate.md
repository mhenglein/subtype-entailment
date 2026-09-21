# Publication candidate — 21 September 2026

Actor: `publication-candidate-20260921`, owner-authorized integrator.
Scope: the requested publication steps 2–4; coordination #37, manuscript #79,
reproduction #65, parent checklist #63. Base main:
`fed560c6682e5ac1e1661d5c60e595f948e768ba`.
Candidate branch: `codex/publication-candidate-20260921`.

## Integration and disposition

| Contribution | Exact author head preserved | Bounded disposition |
|---|---|---|
| #66 / PR #76, raw-summary diagnostics | `986e34b4b61a1ba05a45282bd1f3c84f28103fee` | Integrated diagnostic code and evidence; no measured optimization or n=6 completed answer. |
| #72 / PR #77, graph-only first returns | `910e3071eab494e58e01c53b1e6891186ed73b30` | C090 ordinary schema theorem and E066 component corpus. No generic compiler implementation. |
| #74 / PR #75, function-only analysis | `4ed2fb67458f37b286740a325d91404bb22b58f0` | C091 ordinary characterization and precise nonadditivity obstruction; general function entailment stays open. |
| #72, fixed positive arity | `3fca2e8bf8a0036469867cb528b3ff96b9d9eb96` | C089 ordinary computable reduction and E065 components; no polynomial or finite-tree transfer claim. |
| #67, native terminal diagnostics | `3135cd075e8ce31292fa609d3e9b3a80b2b9bb35` | Reviewed diagnostic follow-up to E061; strict correctness cases and capped stress remain distinct. |
| #68, checked producer core | `049aa110cf13688d4058b1cbecf80aa0fc3a7fb6` | Reviewed contribution deferred: the author has not supplied the promised final source handoff. Branch preserved; [request](https://github.com/mhenglein/subtail/issues/68#issuecomment-5754530885) remains explicit. |

The first five contributions have ancestry-preserving merges. Their ordinary
proof text and corpora remain unchanged; current-status banners link the older
pending-review wording to the accepted review and canonical claims. No Lean
proof definition, default import, production solver or pinned toolchain changes.
The new native driver is a diagnostic caller of existing declarations.

A separate code readback found the native guard rejected any addition under
`lean/Subtail`, including accepted optional modules. The repair enumerates
all protected files present at its base commit and rejects every modification
or deletion of those files, while permitting additional modules. The fresh
native receipt now inventories the driver, full Lean source tree, toolchain,
Lake configuration, CLI and independent fixture source. Historical receipts
and failed launcher attempts remain untouched.

The native branch-only workflow is preserved in merge history, then replaced
by steps in the continuing main/PR Lean workflow. Cheap CI also replays all
three ordinary extension corpora and the release-verdict/provenance guards.
The exact triggers include the changed scripts and experiments. CI does not
run the entire fresh-clone reproduction runner; that has its own receipt.

## Manuscript and contribution review

The paper retains its exact main and finite-tree theorems and the complete
terminal-decision exposition. Section 1.1 now states four separate contributions
and credits the earlier dual-safety observation alongside the leading
Henglein–Rehof account. [Fresh bounded primary-source comparison](prior-work/publication-comparison-2026-09-21.md)
records theorem locators, searches and unresolved priority questions. C086's
smaller bound and C089–C091 are companion results; this review does not silently
expand the manuscript to all repository research.

A separate read-only mathematical reviewer examines the entire manuscript,
critical definitions and declaration boundaries. The integrator owns all
corrections, the primary literature refresh and rendering. This is an agent
review of supplied arguments, with inherited context, not blind rediscovery,
external human refereeing or venue acceptance. Exact findings and final visual
coverage are recorded below.

## Reproduction contract

Run `python3 scripts/reproduce_release.py` on Linux in a clean new clone with
no `lean/.lake`, using Python 3.13.14 and Lean 4.33.1. An ordinary workstation
or remote machine is sufficient; no named private host or cloud provider is
required. Installed toolchain caches are reused; project build caches are not.

The run explicitly builds optional modules, checks the default core,
normalization, C081, finite decisions, certificates and C030, and includes
C082, C086, C087 and the C088 language core. It replays E065–E067, raw diagnostic
guards, native supervisor negative controls, strict native cases and capped
stress. It also runs the original border suite, actual paper examples, a
Lean-checked emitted countermodel, Python tests, the index and declaration map.

Every strict gate must pass its own receipt, not merely return exit code zero.
Native coverage is compared with the exact requested IDs. Diagnostic stress
may remain UNKNOWN, which is reported as DIAGNOSTIC and supplies no answer or
promotion coverage. The PDF must agree with the manifest, current render
inputs and committed input bytes at the render revision. Negative controls
reject changed inputs, a mismatching PDF and incorrect or incomplete coverage.

[Fresh reproduction receipt](../results/publication-reproduction-20260921.json)
records the exact checked revision, source hashes, commands and per-step status.
[Integration/review receipt](../results/publication-candidate-20260921.json)
records review and publication evidence. A missing, pending or failed receipt
is not completion. These files preserve earlier failures rather than relabeling
them as successful checks. Logs are preserved in the committed evidence directory;
private paths are normalized without changing scientific or source-content hashes.

## Review findings, execution and handoff

The whole-paper review found no substantive mathematical blocker within the
stated scope. It covered Sections 1–15 and the dependency/declaration maps,
with selected declaration readbacks in EntailmentDecision, FiniteTreeDecision,
FiniteTreeReduction, RankQueryDecision, InfiniteDecision, RankQueryCoverage,
RankQueryEnumeration, RankQuerySound and ExplicitTopDualProjection. Two wording
clarifications were applied and re-read: priority is distinct from a contribution
claim, and T(r,p) means forward reachability from r to p. This is not an audit
of every transitive declaration.

The separate code reviewer accepted the native source-pin correction, case-ID
and promotion-credit checks, PDF provenance checks and failure-receipt handling
after identifying the gaps. Both reviewers were read-only and ran no builds.
The integrator's local Python suite passes 96 tests; paper mapping checks 23
mapped and seven ordinary results, the scholarship check validates 26 sources,
and the index checks 179 records. No local Lean run is claimed here.

The new PDF has 35 pages. All pages were visually checked in six contact
sheets; pages 4, 27, 30 and 35 also received full-page inspection. Text geometry
checks find no characters outside pages, all expected running headers and
page numbers, and the TeX log reports no missing glyphs or overflowing boxes.
The manifest ties the PDF to committed render inputs at `8a57dd7`.

The fresh Linux execution at `a22d1fb323026fb1c10411d4418ceb03dd2798c2`
passed all **27 run gates** in 313.477 seconds (sum of recorded step times).
It started with a clean checkout and no `lean/.lake`, copied no project cache,
and finished with no tracked/untracked changes. The receipt inventories 363
source files. All 14 strict native cases passed. The six stress cases all
reached the sampled 2,048 MiB process-group RSS threshold and remain UNKNOWN;
no automatic depth-two promotion succeeded. A successful diagnostic gate means
that those inconclusive outcomes were classified correctly, not that the six
problems were decided.

[The complete evidence directory](../results/publication-run-20260921/README.md)
retains 92 raw-output files with path normalization and both original/stored
hashes. Fresh subordinate receipts cover the C082/C086 audits, C087/C088 corpora,
C030 kernel/axiom checks, the actual checked alternating-spine countermodel,
all 96 Python tests and the exact paper example outputs. All earlier receipts
are preserved separately.

After the run, `paper/README.md` received one prose correction: Section 11 uses
finite enumeration to prove a computable bound; it does not expound the explicit
C082/C086 numerical estimates. Every other inventoried source, all executable
code, proof sources, workflows and render inputs/PDF are byte-identical to the
freshly checked tree. Final paper/index checks are rerun on the combined record.
The full fresh run is attributed to its actual revision, not a later commit
that adds its receipt. Published-main/PR/CI readback and final lease release are
recorded in [#37](https://github.com/mhenglein/subtail/issues/37). No final release tag, license grant, author attribution, public
visibility change, branch retirement or external invitation is authorized or
performed by these steps. Older worktrees, stashes and unknown author-local
changes are neither modified nor claimed fully inventoried.
