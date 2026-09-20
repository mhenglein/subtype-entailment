# Reviewed repository reconciliation and completion map

Date: 2026-09-20. Actor: Astra, `reconcile-prs-20260920`.
Base main: `bfa50cc53e8d6f5d7699cc699ceb266a8686168b`.
Owner instruction: merge every PR, close stale issues and create the remaining
work before calling the project done. Lease:
[#37](https://github.com/mhenglein/subtail/issues/37#issuecomment-5749924173).

## Result and preserved ancestry

| PR | Exact original head | Integration |
|---|---|---|
| #44 | `99d951077ace1c93d0fec604839674fb3f19dbc9` | Original semantic audit retained; then-open obligations labelled historical |
| #45 | `c33d0c8d65158fc7ba53e5bc24c14132f071dc42` | Ordinary normalization proof, proposed interfaces and adversarial cases retained |
| #47 | `42be43f35a98d4d23a4ba26439833730bbcd6510` | Counterexample/checker/result retained; one compiler-note conflict resolved without losing the newer C082 correction |
| #51 | `db55acded6064b12d5d483216e29653ae3d884f3` | Unchanged direct C030 Lean sources, audit fixtures and original certification note retained |

The four actual merge commits are `641c9bc`, `72fa86c`, `4147f63` and
`ef40fbb`. All four original heads are ancestors of the integration branch.
Current-status notices were added after those merges; the historical bodies
and exact original commits remain available. No old proof is silently replaced
by the proposed interfaces in an advisory note.

Only `research/RANK_QUERY_COMPILER.md` conflicted. Its current C082 correction
stays first; the original September 19 discovery follows with its old pending
review status explicitly dated. The original F alone and a smaller existential
compiler are still open. The same checker/result bytes are preserved and replayed.

The C030 modules remain optional and independent of the default forward-proof
aggregator. Their dedicated workflow now runs on main and all Lean dependency
changes, both checker scripts, the archived regression and the workflow itself.
It also supports manual dispatch. The earlier branch-only trigger could miss
future semantic changes; no shared 40-minute Lean job is enlarged by this repair.
Existing Lean definitions, paper/PDF/source pins, toolchain and benchmarks are
unchanged. The separate new C030 job has a 15-minute cap.

## Independent review and exact C030 statement

Two bounded read-only reviewers worked alongside the parent integrator. The
C030 reviewer read the ordinary proof and then the Lean definitions and critical
implications at the exact PR head. This is a separate source/statement review
informed by the argument, not blind rediscovery or human peer review. It found
no mathematical or statement blocker and identified the missing main/dependency
workflow triggers, now repaired.

For every `I : Instance k` such that every final state has both transitions
undefined, the executable finite list `constraints I` uses `Fin (2*k+1)`:
upper-copy variables `a_q`, lower-copy variables `v_q` and one denied bottom
variable `b`. It is satisfiable over arbitrary prefix-closed binary path sets.
For every unchanged finite word `w`, `Witness I w` holds exactly when some
model contains `w` in `a_initial` and omits it from `v_initial`.
The final non-entailment corollary quantifies over those arbitrary-tree models.

The reviewer checked:

- the actual list-to-`Laws` equivalence, denied undefined-transition target,
  lower clauses exactly at nonfinal states, and ordered flag `a_p <= v_q`;
- every-prefix safety, final acceptance, all `i <= j` suffix comparisons,
  including diagonal, empty-word and full-suffix boundaries;
- separation-to-witness transport and the explicit prefix-closed witness model,
  including propagated flag seeds and forced lower roots;
- the theorem's arbitrary-tree domain and the forced infinite-spine fixture;
- dependencies: no forward canonical/summary theorem, C029 or numerical bound.

`realization_satisfiable` and `witness_iff_separating` use only the terminality
hypothesis on I. The non-entailment theorem inherits classical choice through
the existing semantic separating-address theorem; executable constructors
remain choice-free. **Fixed-budget preservation is not proved by these Lean
declarations.** Its ordinary proof and existing reproduction remain separate,
with formalization tracked in [#73](https://github.com/mhenglein/subtail/issues/73).

The historical-patch reviewer compared the original PR files and merged blobs,
checked the sole conflict and the distinction between a refuted universal
concrete U, a corrected bound and the unaffected original F question. It found
no blocker. Neither reviewer ran the native commands below. Their scope did
not include a fresh global literature review or a lemma-by-lemma reproof of
the already integrated C081/C082 developments.

## Fresh combined-tree validation

Checked source revision: `036c64f2268f60955c33cb3c40fd0d483182912f`.
Host: isolated wb-marcus worktree, Linux aarch64, Lean 4.33.1, Python 3.13.14.
The cache was copied to the new checkout; no active build cache was shared.
This is a fresh build/kernel execution, not a cache-free release installation.
Later record changes preserve all 69 recorded Lean source hashes.

[Complete commands, source hashes and dependency readback](../results/repository-reconciliation.json).

```sh
cd lean
lake build +Subtail.TerminalRealizationAudit
lake env leanchecker Subtail.TerminalRealization
lake env leanchecker Subtail.TerminalRealizationModel
lake env leanchecker Subtail.TerminalRealizationAudit
# Execute the complete declaration-audit block in .github/workflows/lean-c030.yml.
cd ..
python3 experiments/replay_c030_independent.py --output /tmp/c030-replay.json
python3 scripts/check_lean.py
python3 experiments/check_rank_query_weight_counterexample.py > /tmp/weight.json
cmp results/rank-query-weight-counterexample.json /tmp/weight.json
```

All commands pass. The declaration audit covers all 72 named declarations and
checks all seven executable constructor dependencies for classical choice.
Only `propext`, `Quot.sound` and, where permitted, `Classical.choice` occur;
there is no custom, sorry or native-evaluation axiom. The exact-tree replay
matches the archived semantics on 12,956 instances and 200,196 word/model
checks, including 416 positive words, baseline satisfiability models and the
separate counterexample after deliberately dropping terminality.
The concrete weight counterexample output is byte-identical to its PR result.

The default check runs `lake build`, `leanchecker Subtail`, core axiom readback
and independent Python/Lean regressions. It does not newly run every optional
module/benchmark audit in the full GitHub Lean workflow. The C030 Python wrapper's
`not_run` fields describe that wrapper only; the separate native proof steps
did execute. Local independent border experiments also pass without changing
the tracked deterministic receipt. A mistakenly used module-style unittest
command failed to resolve its local import; the documented discover command
passes all 13 navigation tests without a source change. Paper declaration,
source-map, bibliography and literal-example checks pass; no PDF was rebuilt.
Final index/diff/workflow guards and published-main CI status are recorded
in the closing #37 handoff. A queued or skipped CI job is not a passing check.

## Issue disposition and remaining work

[The completion map](../research/COMPLETION.md) and
[#63](https://github.com/mhenglein/subtail/issues/63) now distinguish final paper
and reproducible-release gates (#64/#65) from stronger research (#66–#73).
The latter covers raw-summary cost, terminal-promotion stress, verified producer,
original C080 questions, tight complexity, explicit top, other signatures and
C030 budget certification. No issue creation launches a worker.

Close #23/#28/#33 as completed at their actual semantic/closure/readback scope.
Close #32 as superseded with its unexhausted stress scope transferred to #67;
its capped fixture searches are not relabelled complete. Close #30/#34 as
superseded by C081/C082 and the two exact unresolved questions in #69.
The old issues keep history and receive precise evidence/replacement links.
The final publication handoff records the actual closed states; this note is
not a claim that an issue operation succeeded before its readback.

Keep #37 as the standing integration channel. Licensing remains pending and
author/affiliation placeholders stay as requested. No human referee, new license,
new release tag or original-archive task is created. The main scientific theorem
is complete; the release and broader programme retain the explicit remaining
gates. Historical branches and worktrees are not retired. Unowned uncommitted
files, stashes and unpushed work were not inspected or deleted.

Release every parent/reviewer scope after the verified non-forced main update
and final issue/PR readback. No background researcher remains assigned by this
reconciliation; automatic CI may continue at the exact reported status.
