# Finite-tree paper revision and readback

Date/session: 2026-09-20, paper-finite-20260920. A010/A018, C085; #59/#37.
Base: `341f2d041832e3e18faaf02e88621f11c402a342`.
Status: manuscript and artifact revision complete; integration evidence is in #59/#37.

## Target, route and ownership

Add the checked finite-expression decision to the standalone mathematical
paper, without abbreviating its existing terminal proof or placing research
administration in the manuscript. Reuse the mature
[finite-tree route](2026-09-20-finite-tree-decision.md): finite reverse-pop
automaton, consuming-cycle obstruction, no-cycle word bound, finite canonical
closure, model/query transfer, and finite-preserving normalization. No new
mathematical assumption or Lean declaration is required.

The paper must define the finite automaton and prove both branches, give
finite/arbitrary disagreement and no-growth unsatisfiability examples, and
identify exactly which declarations check which result. Preserve the seventeen
old source pins and add a separate finite-decision pin. Finite satisfiability
and the displayed seed-dependent numerical estimate keep their ordinary-proof
status where no identical Lean endpoint is provided.

Parent owns all manuscript, artifact, comparison and canonical-record edits.
The mathematical reader is read-only and previously authored `PopAcyclic`, so
its review is not blind independence. The separate literature reader checks
primary HR97/HR98/NP99/NP03 statements, including constructor and tree domains.
Neither reviewer owns files or shares a Lake build. Issue #59 records scopes
and releases; #37 holds the integrator lease.

Open presentation obligations at entry: manuscript-only completeness of the
finite proof; exact correspondence to checked declarations; precise finite-tree
comparison with the older results; reproducible multi-revision maps; polished
PDF. Literature non-subsumption and global priority are not assumptions of
this task. Existing proof, solver, complexity and experiment claims are fixed.

## Validation plan

Run paper source/map/literal/citation guards, research navigation and bounded
scholarship checks. Execute the revised small Lean example on the pinned
toolchain in an isolated checkout. Theorem source is unchanged: a new PDF is
not a new replay of the full proof. Record checked revision and artifact hashes,
inspect the rendered PDF, then publish by non-forced fast-forward after fresh
ownership/main readback. Author placeholders and pending licensing remain.

## Result and semantic readback

Theorem 1.2 states the unconditional finite-expression decision. Section 13
defines the finite epsilon NFA and its consuming-cycle test. Lemma 13.1 proves
the consumed-word bound from distinct boundary controls; Lemma 13.2 uses the
forced target of a reversed push to exclude finite models. Minimum-stack
factorization gives the finite-seed closure estimate. Theorem 13.3 proves
finite entailment is growth or arbitrary entailment, and finite-preserving
normalization yields Theorem 1.2. Corollary 13.4 treats finite satisfiability
separately. Three examples distinguish growth, a finite countermodel, and
unsatisfiability without growth.

The original Sections 5–11 are byte-identical to their text at `341f2d0`.
This revision does not compress or replace the terminal-decision exposition.
All Lean source files, solver scripts, theorem statements and prior receipts
are unchanged. The map now has twenty-one checked entries and four ordinary
consequences. Seventeen entries retain `c946d86`; the four finite entries use
`4159c58`. Each source file is byte-compared with its exact immutable pin.
CI now fetches both revisions in its shallow checkout before checking the map.

## Reviews and corrections

The mathematical reader checked the frozen draft `ddb3ff0` against the exact
finite definitions and declarations. It covered cycle orientation, the
balanced-prefix rotation, forced growth, repeated controls, empty seeds and
zero-control boundary cases, seed dependence, finite naming and example scope.
It found no core blocker and requested five local presentation corrections:
define normalized finite entailment, name every graph edge class, identify
contraposition, qualify the balanced relation and normalize the example, and
give the exact map count. All were applied and rechecked at `a3453ed`.

- [Draft review](https://github.com/mhenglein/subtail/issues/59#issuecomment-5747949861)
- [Correction check and scope release](https://github.com/mhenglein/subtail/issues/59#issuecomment-5747968661)

The reader previously authored `PopAcyclic`: this is a separate review of the
parent's exposition and its source correspondence, not blind independent
discovery or human peer review. It did not reread all earlier Sections 5–12.
Those sections retain their earlier review record.

The literature reader checked primary HR97, HR98, NP99 and NP03 statements,
signatures and finite/regular/arbitrary domains, then reviewed their integration
at `a3453ed`. The finite comparison names HR98 Theorem 2 and NP99's semantic
top; the introduction states NP03's positive arity and shared word equation.
Its two final wording suggestions were applied in the dated comparison note.
The older HR98 access limitation is visibly corrected without changing the
historical note. No priority, full-input PSPACE or non-subsumption theorem is
inferred. [Dossier](prior-work/finite-tree-comparison-2026-09-20.md),
[primary review](https://github.com/mhenglein/subtail/issues/59#issuecomment-5747928334),
[integration review and release](https://github.com/mhenglein/subtail/issues/59#issuecomment-5747968663).

## Reproduction evidence

### Lean example: fresh remote build and execution

Host: wb-marcus, Linux aarch64, Lean 4.33.1. Isolated checkout:
`/home/marcus/workspaces/subtail-worktrees/paper-finite-20260920` at
`ddb3ff04dc30d0400f4144fc1f82e156f778c6ec`. Commands, after loading the existing
Subtail environment:

```sh
cd lean
lake build +Subtail.FiniteTreeDecision
lake env lean --run ../paper/example.lean
```

PASS: 49 build jobs and all four displayed results:

```text
With premise x <= y, query x <= y: true
With premise x <= y, query y <= x: false
With premise x * bottom <= x, query x <= bottom (arbitrary): false
With premise x * bottom <= x, query x <= bottom (finite): true
```

The executed example's SHA-256 is
`8402bbf80bee2bfdaa01a373716c5f2571b5667b38588d45d927403869fe65eb`;
its bytes are unchanged in the final contribution. The remote checkout was
clean after execution. The full kernel replay and dependency audits were
**NOT RUN anew** for this documentation-only revision; their source-pinned
finite-decision evidence remains in the earlier readback. No benchmark speedup
or new regression census is claimed.

### PDF and local checks

The final render source revision is
`85cb2903fcaa2cc4b789e7f24aab23309ab34a8a`. Pandoc 3.11 and Tectonic 0.17.0
produce 28 A4 pages, 203467 bytes. The manifest records both proof revisions,
all source hashes and `source_files_match_render_revision: true`. PDF SHA-256:

```text
a12615cc30dc0e8fd8acfc1728730f7780784428e13ae200775537b013a69f9e
```

All 28 pages were rendered and inspected in contact sheets. The title and
contents pages were inspected individually; pages 24–28 were also inspected
at 135 dpi for the new proof, notation, examples, formalization and references.
An initial 29-page version overflowed its contents by two entries; reducing
only the contents font keeps the full hierarchy on one page. No clipping,
missing glyphs, overlapping text or overfull/underfull boxes were found in
the final render. The log retains a harmless unused table-caption setup warning.
Review images are temporary and excluded from Git.

Local acceptance commands are:

```sh
python3 paper/check.py
python3 scripts/research_index.py --check
python3 -m unittest discover -s scripts -p test_research_index.py
python3 notes/prior-work/check_scholarship.py
git diff --check
```

All five commands PASS on the combined contribution: 13 navigation tests,
18 approach records, 163 A/C/E/Q entries, and the scholarship guard's 26 source
records and 129 local links. Its two literal regressions also pass. These
document checks do not perform mathematical proof review.

The paper guard checks 21 mapped results, four ordinary results, declarations,
source identities, bibliography keys, literal examples and absence of research
administration in the manuscript. Source and PDF hashes were independently
recomputed. The final integration comment in #59 records the combined checked
commit and CI status; historical results are not relabelled as fresh runs.

## Limits and next question

This completes the exposition and artifact step, not a new mathematical
extension or complexity result. The finite-SAT Boolean, explicit top, other
constructor/variance signatures, producer formalization, exact novelty and
remaining E055 timeouts stay separate. Author/affiliation placeholders and
pending licensing are unchanged. The best next practical question is which
construction dominates the deeper E055 cases under matched resource caps;
profile before selecting another representation change.

The parent releases all owned paths at the integration recorded in #59/#37;
both reviewers have released their read-only scopes. No historical branch,
stash or uninspected workspace is retired. No work continues in the background.
