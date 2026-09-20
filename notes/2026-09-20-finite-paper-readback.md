# Finite-tree paper revision and readback

Date/session: 2026-09-20, paper-finite-20260920. A010/A018, C085; #59/#37.
Base: `341f2d041832e3e18faaf02e88621f11c402a342`.
Status: revision in progress; review and final render evidence follow below.

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
