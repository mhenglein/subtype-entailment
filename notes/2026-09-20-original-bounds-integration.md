# Original terminal witness bound: reviewed integration

Date: 2026-09-20. Session: `issue69-integration-20260920`.
Workstreams A017/A018; claims C080/C082/C086; issue #69 and PR #78.
[Integration scope](https://github.com/mhenglein/subtail/issues/37#issuecomment-5750999463),
[scope refinement](https://github.com/mhenglein/subtail/issues/69#issuecomment-5751037614),
[machine-readable receipt](../results/original-bounds-integration-20260920.json).

## Result

[C086](../research/claims.md#c086) proves two exact obligations from #69:

1. A computable smaller compiler satisfies the original semantic and
   clause-weight contract, with `U_k(T)=64*k*T^(2*T+2)`.
2. The original terminal witness bound F holds for the original binary
   `Witness` predicate, assuming only that final states are terminal.

This is a new compiler with a proved contract. The old unfiltered compiler
still violates U, as the existing five-state counterexample proves. C082's
larger bound remains valid independently. The production C081 solver and its
default import graph are unchanged. No measured speedup, tight complexity
class, broader constructor signature or publication priority is asserted.

## Exact mathematical readback

For a clause c, let a be its number of path atoms and S the sum of their
observer state counts. The new compiler enumerates the same finite diagrams
as before, retaining only those with at most `a+S` active coordinates on each
physical interval. This syntactic test does not inspect a reference, extension,
assignment or generated word. It preserves occurrence multiplicity.

For every binary instance I, every query phi and every safe reference B,
`SmallerCompilerAstra.closureFor` proves

```text
Sat(prefixGraph I B, preSmall I phi)
  iff exists C, FirstReturnExt I B C and Sat(prefixGraph I C, phi).
```

It also bounds every retained clause by `U_k(weight(phi))`. The compiler contract
does not need terminal-finality. Coverage uses product-simple atom runs on one
fixed common extension; reconstruction retains one common generated word.
Neither proof replaces one conjunction by separate per-atom witnesses.
The empty query produces no clauses. Repeated coordinates, shared intervals,
zero-length pieces and coincident marks remain covered.

Put `T_0=k+10` and `T_(j+1)=64*k*T_j^(2*T_j+2)`. Then

```text
F(1)=0;
F(k)=2*(k+1)*product_(j=1..k-2)(T_j+2), k>=2.
```

`FOnlyCompilerBridge.original_F` proves that a terminal instance has any
witness iff it has one of length at most F(k). In particular F(2)=6. The
runtime value at zero is 2; an `Instance 0` cannot exist. The bridge has no
caller-supplied compiler contract, coverage theorem, absorption condition or
witness cap. It extracts a retained concrete diagram and invokes
`RankQueryLengthBound.compile_bounded`, then unwinds the same shared-reference
chain. Clause size alone would not justify this word-length argument.

The [author's alternative FinishPlus route](2026-09-20-f-only-astra.md) remains
ordinary mathematics with selected checked lemmas. The complete checked
composition used here is the smaller-compiler bridge. No second full Lean
composition is claimed.

## Provenance and integration changes

The integration started from main
`9f4b95784a212c322c48a957b80645a1077543ed` and retained author ancestry:

| Contribution | Reviewed head | Integration |
|---|---|---|
| Smaller compiler, PR #78 | `db0a6d3505e93ff6bc51a8d89fcb52fb05adfe0f` | Merged first |
| Original F, #69 | `6aa7047cc6cbccd44c64223209b7563cf2824b8e` | Merged after its compiler dependency |
| Nine-submission review | `2ffdbd8384f5d98aa257d476c1901cfc3deddd8f` | Imported note/receipt with original reference |

The three Lean modules, two Python checkers and two author receipts are
byte-identical to those reviewed heads. The compiler Lean source also matches
the earlier checked compiler dependency at `acf0524ffdbc9f407797b68b8953a39e1f79cf5d`.
The F author released all six delivery paths. The owner-authorized coordinator
explicitly accepted the exact published compiler blobs for integration; this
does not claim the compiler author released unknown local work or stopped
working. No author worktree or branch was reset, rebased or deleted.

The two branch-only workflows are replaced by one continuing step in the
existing main/PR Lean job. The old F workflow's historical-source overlay is
removed. The new [checker](../scripts/check_original_bounds.py) always builds
the current combined source. It explicitly compiles the two root-level F files,
which the default `Subtail` aggregator does not import, and kernel-replays all
three modules. It audits 22 compiler, 20 F and 6 bridge declarations. Theorems
permit only `propext`, `Quot.sound` and `Classical.choice`; all nine public runtime
definitions exclude choice as well. Native guards check F(1), F(2), rejection
of the old oversized diagram and the empty-query output. Logs and receipts
are uploaded even on failure. A wall-clock timeout is UNKNOWN and fails CI.

Independent Python checks replay the literal compiler corpus, the unchanged
repository compiler counterexample and the F diagnostic corpus. Saved semantic
receipts must agree; only environment/time fields are ignored for the F run.
These checks are explicitly bounded evidence, not substitutes for the proofs.

## Review and fresh validation

The [nine-submission review](2026-09-20-submission-review.md) separately records
the original proof review and native reproduction. During integration,
`publication_proof_review` read the declarations back into ordinary mathematics
and accepted the C086 hypotheses, quantifiers and boundary from the old compiler.
That read-only review did not rerun builds or change files.
`historical_pr_review` separately reviewed continuing CI and its failure paths.
Its two concrete hardening findings were fixed: include the Lake manifest and
gate tests in source hashes, and tolerate a process group exiting during timeout
cleanup. The declaration inventory checks all current public declarations and
requires critical names; source review still checks their intended statements.
A whole-job CI cancellation is a separate failure, not a mathematical verdict,
and may occur before the final Python receipt is written.

Fresh validation used an isolated Linux AArch64 workbench checkout, existing
Lean 4.33.1 and Python 3.13.14, and an initially empty project Lake cache.
The source/checker revision was
`92680b0630de86fbe5ca3aa323fa97cdd0b6ecaa`:

| Check | Outcome | Seconds |
|---|---|---|
| `python3 scripts/test_check_original_bounds.py` | PASS; malformed, missing, duplicate and forbidden dependency cases | 0.091 |
| `python3 scripts/check_original_bounds.py` | PASS; build, three kernel replays, all 48 closures, native and Python regressions | 61.805 |
| `python3 scripts/check_rank_weight_native.py` | PASS; old counterexample and larger C082 proof remain checked | 10.481 |
| `python3 scripts/check_lean.py` | PASS; default build/kernel and existing independent core comparisons | 173.662 |
| Existing `results/lean-checks.json` byte readback | PASS; unchanged; remote tracked tree clean | — |

After the checker-only hardening, the five gate tests and complete new gate
passed again at `a33fb055be1473b025380c105a6a2883d35a5385`, in 0.128s and
12.052s respectively. This second run reused the first run's project cache.
It still explicitly replayed all three kernels and all diagnostics. No Lean
or author Python source changed; the existing core/quantitative results above
remain pinned to their original checked revision.

The receipt distinguishes these fresh source checks from later documentation
checks and hosted CI. Source hashes identify exactly what was tested; a later
note-only commit is not relabelled as a fresh native run. The complete existing
hosted CI matrix was not duplicated on the workbench. Its main run is read
back separately at publication.

## Remaining work and handoff

The exact original-F and existential smaller-compiler obligations are complete.
Filtering occurs after diagram enumeration; no practical speedup follows, and
clause weight does not bound disjunct count or execution time. C082's published
paper proof remains valid; this integration does not rewrite the paper/PDF.
Integrating C086 into that exposition is a separate editorial task.

Other accepted submissions retain their separate integration gates. In
particular, producer/top modules still need continuing CI before publication.
The #67 native follow-up was released at `3135cd075e8c` during this integration.
Its new diagnostic handoff remains untouched and awaits its own review.
Issue #69 closes only after actual main publication. The final #37/#69 readback
records the main revision, hosted CI state and explicit release of this lease.
Uninspected local work, other branches and stashes remain preserved.
