# Finite-tree reduction: mathematical and source readback

Date: 2026-09-20. C085, E056, A010/A018; coordination #58/#37.
Parent: finite-trees-20260920. Independent mathematical/code reviewer:
finite-tree-review-20260920 / finite-tree-implementation-review-20260920.
Lean author: finite-tree-proof-20260920 (saturation-author-20260920 in the
source handoff). The repository records these as distinct agent roles, not
human authorship or publication credit.

## Source and review boundaries

Base main was `bb9295429ccdeb0cdbad5655e30582eaf77f6361`. The parent outline
was committed before implementation at `e420963`. The first complete ordinary
proof, classifier, finite interface and independent experiment were pushed at
`cf17101323793295e996b7a5acf53f7497af25e0`. The isolated Lean contribution
`9c2f730fecf9c7bca94a408162be79ce126646e8` was integrated unchanged at `0a81ffe`,
after its source release in #58. Parent validation first checked `0b772bb`,
then checked `8f6fad6` after a diagnostic fixture correction. The full SHA and
all relevant source hashes are in [the receipt](../results/finite-trees.json).

The ordinary proof reviewer first checked the proposed Hot-denial reduction
without relying on a Lean proof. The parent subsequently proposed the stronger
consuming-cycle simplification, which the reviewer then checked. This is
independent mathematical review of an explicit argument, not independent
rediscovery. The reviewer confirmed minimum-stack orientation, necessary
denials, finite-closure replacement, the forced-root cycle argument and
finite-valued normalization. No mathematical blocker was found in that scope.
The exact argument appears in [the proof note](2026-09-20-finite-tree-reduction.md).

The independent implementation reviewer checked `8f6fad6`, including the
malformed-result guard and corrected cold-unsatisfiable fixture. The review
found no correctness blocker in reverse-pop orientation/completeness, forced
roots, rooted graph finiteness, zero-variable/query-only syntax or UNKNOWN
handling. It confirmed the SAT census's limited scope. [Exact source-pinned
report and release](https://github.com/mhenglein/subtail/issues/58#issuecomment-5747715457).
The reviewer made no edits, builds or Lean runs; those checks were performed
separately by the author and parent on the revisions named below.

## Exact Lean readback

The parent independently read the 396-line source and its unchanged imported
contracts at the worker pin. It is an optional module, explicitly built and
replayed by the new checker; the default import aggregator is unchanged.

| Declaration | Meaning and actual hypotheses |
|---|---|
| `FiniteTree X` | There exists N such that every product address of X has length < N. Binary branching makes this equivalent to a finite product-node set. |
| `BoundedReversePop M m`, `Hot M m` | A bound uniform over all initial controls q for Pop(reverse M,q,w,m), and its negation. Finite control cardinality makes this agree with the ordinary fixed-q infiniteness definition. |
| `closureBounded_iff_noHot` | For any finite control system and finite seed list, the full seeded reachability closure has bounded lengths exactly when no reached control is Hot. No algorithm for Hot is supplied. |
| `canonicalFinite_iff_noHot` | The same property for all component trees of the existing canonical prefix-seeded valuation. |
| `forced_reverse_pop_loop_noFiniteModel` | A supplied forced root and a supplied nonempty reverse-Pop self-loop exclude finite satisfiability. The theorem does not locate such a root or loop. |
| `finiteEntails_iff_entails_of_uniform_reverse_pop` | Under an explicit `UniformReversePopBound (systemOf C)` assumption, normalized finite entailment equals arbitrary entailment. No such bound is computed here. |
| `normalize_finite_entails_iff` | Finite-expression entailment is equivalent to finite entailment of the existing Lean normalization. Finite values extend by structural induction and restrict to original variables. |

The closure proof uses `reaches_normal` with words `u=x++z`, `v=y++z`; the
reverse Pop word is prepended to the fixed suffix. The finite-control maximum
combines only bounds for reached controls. The forced-loop proof repeats the
nonempty word at an already forced product root and contradicts that root's
finite bound. The entailment proof extracts the existing canonical separator
from arbitrary non-entailment, proves all its component trees finite, and
applies finite entailment to that same model. There is no hidden satisfiability
promise, changed query semantics, finite search premise or replacement of
arbitrary non-entailment by a bounded search.

All 31 named declaration dependency closures were audited. The 13 non-theorem
definitions are free of Classical.choice; theorems use only propext, Quot.sound
and Classical.choice. There is no added axiom, incomplete proof, opaque or
unsafe implementation, implemented_by replacement, or native_decide proof.
The proposition definitions do not pretend to be a computable classifier.

The unresolved formal bridge is **global graph classification**: a positive
classifier must provide a nonempty loop at a forced root; a negative classifier
must provide a uniform reverse-Pop length bound. Those implications are proved
in ordinary mathematics, but no executable Lean Boolean correctness theorem
composes them with the checked semantic endpoints. Python DAG naming also
remains separate from the existing checked Lean normalization.

## Fresh validation and reproducibility

Use the pinned Lean 4.33.1 toolchain. Long validation ran on wb-marcus, Linux
aarch64, in its own `/home/marcus/workspaces/subtail-worktrees/finite-trees-20260920`
checkout. No active worker shared its Lake build. Existing toolchain/runtime
and Git access were checked before use.

```sh
python3 scripts/check_finite_tree_reduction.py --output tmp/finite-trees.json
python3 experiments/check_finite_trees.py --output tmp/finite-tree-experiment.json
python3 scripts/check_lean.py
python3 -m unittest discover -s scripts -p 'test_finite_trees.py'
python3 scripts/research_index.py --check
```

At `8f6fad6`, the new check passes module build and kernel replay, all 31
declaration audits, 13 finite-mode tests, 24 existing CLI tests and 9 extraction
tests. E056 compares 300 finite systems against an independent predecessor-
saturation infiniteness oracle. It also exhausts every set of up to three
normalized clauses on one/two controls: 1,809 inputs and 44,880 finite
valuations. There are 636 satisfiable inputs, 1,147 growth obstructions and
26 unsatisfiable inputs without growth. Every answer agrees.

The finite-SAT census enumerates heights at most n. Completeness of this cutoff
follows from the least forced-root closure bound, not from empirical absence
of taller witnesses. This cutoff is **not** asserted complete for entailment.
The literal finite-tree predicate is independent of the graph classifier and
minimum-stack implementation. The language comparison uses a separate
unbounded predecessor-saturation algorithm, not another SCC implementation.

Seven actual CLI cases pass: growth/vacuity, contradiction without growth,
finite negative variable and ground queries, the same growth input under
arbitrary semantics, rejection of its infinite graph under finite semantics,
and a capped run returning UNKNOWN. Three cases include successful C084 kernel
instance proofs. These certify arbitrary non-entailment of the emitted original
expressions; finite graph height remains independently checked Python.
The full output, timing, commands and trust messages are retained in the receipt.

The unchanged default core separately passed `scripts/check_lean.py` on wb at
`0b772bb`: default build, `leanchecker Subtail`, core axiom checks and existing
differential regressions, with zero failures. The later fixture/checker
correction changed no Lean or core source. The receipt retains this exact pin
and the unchanged `results/lean-checks.json` hash. This is not a claim that
every optional module audit or the entire CI workflow ran locally.

## Supplementary independent classifier probe

The reviewer additionally ran 5,000 systems: seed 1739, 1,000 cases at each
n=1..5, epsilon probability .15 and push/pop probability .12, alphabet {0,1}.
Every generated push target was marked forced; no denials were added. This
ran before the final fixture correction; that commit changed no classifier
source. All Hot endpoints agreed with the independent predecessor oracle.
This is supplementary reviewer evidence, separate from the parent-run E056
receipt and formal audit. Its exact reproducible command was recovered in the
handoff; the parent did not rerun it merely to duplicate the result.

```sh
PYTHONDONTWRITEBYTECODE=1 PYTHONPATH=scripts:. python3 - <<'PY'
import random
import finite_trees as f
import regular_countermodel as r
from experiments.check_finite_trees import threshold_hot
rng = random.Random(1739)
for n in range(1, 6):
    for i in range(1000):
        eps = {(p,q) for p in range(n) for q in range(n) if rng.random() < .15}
        push = {(p,a,q) for p in range(n) for a in (0,1) for q in range(n)
                if rng.random() < .12}
        pop = {(p,a,q) for p in range(n) for a in (0,1) for q in range(n)
               if rng.random() < .12}
        system = r.System(n, eps, push, pop, {q for _,_,q in push}, set(), 0, 0)
        got, expected = set(f.growth_analysis(system)['hot']), threshold_hot(system)
        if got != expected:
            raise SystemExit((n, i, got, expected, system))
print('growth classifier matches independent threshold oracle: 5000 random systems, n=1..5')
PY
```

## Corrections and rejected strengthenings

The first CLI contradiction fixture was bottom×bottom<=bottom. It is indeed
unsatisfiable, but shared bottom naming also creates a consuming cycle. Thus
its passing result did not cover a no-growth, arbitrary-unsatisfiable input.
The parent replaced it with x×x<=bottom and added an explicit no-growth
assertion. The new diagnostic was rerun. The initial `0b772bb` receipt is
retained as `initial_validation`, with that limitation; it is not relabelled
as the corrected run. This correction did not change the theorem or solver.

The stronger claim that all arbitrary models become finite in the no-growth
case is false: x<=y admits infinite valuations. Only finite canonical
replacements are guaranteed. Tests preserve this distinction. Also, a generic
pushdown cycle whose push target is unforced need not exclude finite models;
the generic `growth_analysis` reports only consuming-cycle existence. The
normalized-input `analyze_problem` checks the required forced-root condition
before applying the finite-model interpretation.

## Remaining scope and handoff

C085 supplies the ordinary all-input finite-tree decision and selective checked
semantics. Its complete executable classifier, finite graph certificate
finiteness proof, and fully checked extractor remain formalization tasks.
Original E055 decision timeouts and C080 F are unchanged. Explicit top and
other signatures require their own arguments. The paper/PDF and original
C081/C084 sources remain unchanged; no novelty or publication-priority claim
is made. Licensing remains pending and author information remains placeholder.

The next focused step is an executable Lean growth classifier with the two
contracts above, using the current finite balanced relation. Preserve the
same endpoint hypotheses until their graph bridge is proved. Integration,
publication checks and release of all session scopes are recorded in #58/#37;
this note does not assign a future worker or imply background work continues.
