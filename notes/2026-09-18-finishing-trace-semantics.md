# Lean: exact finishing-query semantics and direct witness soundness

Workstream A018/C080, stage-5 finishing interface; issue #30, tracker #34.
Base: `a4e9dfcdcf41abf9c14f4e7c2977e9cb530b5c74`.
Branch: `lean/finish-query-facts-2026-09-18`.
Checked proof commit: `fa4f1b07076a6fc977ec9ee0420b9da9b6ec1909`.

**Status: locally compiled and kernel-replayed under the pinned Lean 4.33.1;
all 62 named declaration/constructor audits pass. This is a completed finishing
interface, not a proof of `ClosureFor`, the final witness bound, the complete
rank decision schema, or unrestricted subtype entailment. C080 remains a
candidate. No independent human review is claimed.**

Source: [local move facts](../lean/Subtail/RankQueryFinishFacts.lean),
[trace and completion proofs](../lean/Subtail/RankQueryFinishTrace.lean).
Evidence: [compact record](../results/finishing-trace-semantics.json),
[independent checker](../experiments/check_finishing_trace.py).

## 1. Exact checked endpoints

All statements use the existing `RankQuery.finishQuery`, literal `prefixGraph`,
`SafeReference`, and `Basic.Witness`; none substitutes a new query or witness
predicate. The trace module imports `RankQueryFirstReturn` and the finishing
facts, not the diagram compiler or its soundness theorem.

For a safe nonempty labelled reverse reference B, the principal equivalence is:

```text
finish_iff_no_return_completion:
  Sat (prefixGraph I B) (finishQuery I)
  iff there exists C with
    SafeReference I C,
    B.word a prefix of C.word,
    C.label j = B.label j for every j <= |B.word|,
    C.label |C.word| = I.initial,
    and no later prefix of C has a border of length |B.word|.
```

The last condition, `NoReturn B C`, quantifies over
`|B.word| < j <= |C.word|`. It includes the ultimate cut and overlapping returns.
An empty continuation C = B is permitted.

The soundness endpoint is directly about the original problem's finite-word
witness definition:

```text
finish_implies_witness:
  SafeReference I B -> Sat (prefixGraph I B) (finishQuery I) ->
  exists ext : List (Bool x Fin k),
    Witness I (B.word ++ ext.map Prod.fst).reverse
```

No `TerminalFinals`, `ClosureFor`, rank bound, search cutoff or supplied solver
is a hypothesis of this soundness theorem. Safety of the base remains essential.

The maximal-rank completeness endpoint is:

```text
maximal_rank_completion_finishes:
  SafeReference I B -> SafeReference I C -> Extends B C ->
  C.label |C.word| = I.initial ->
  (forall j <= |C.word|, rank (C.word.take j) <= rank B.word) ->
  Sat (prefixGraph I B) (finishQuery I)
```

Here `Extends` records both the literal word prefix and old-label agreement.
The last theorem derives no-return from actual word ranks using the existing
`no_return_after_maximal_rank`; it does not supply no-return as an unexplained
field of a certificate.

## 2. What the proof does

`finish_move_iff` and `finish_step_iff` unpack the actual observer's transition
table. Each transition emits a bit along a directed K edge, follows a genuine
reverse transition of the original machine, and checks Bad, diagonal flags and
the destination's incoming mask. Source permission comes from `Run`, not from
`Step` alone. The observer's initial control is distinguished from its current
control throughout.

`Trace` records one finite sequence of emitted bits and actual original states.
Every cursor remains strictly below the old reference length. Empty traces are
allowed. `sat_finish_iff_trace` proves both directions between this trace and the
existing query, including its unique endpoint, failure edge, initial control and
original initial-state final control. Consequently `finish_check_correct`
connects the existing finite `satCheck` to existence of an arbitrarily long
finite trace for a supplied reference. It is not a global witness-existence
algorithm.

Appending the trace one letter at a time gives `extend B ext`. The key invariant
is that its literal longest proper border has exactly the old-graph cursor's
length. The checked `parent_next` and `advance_prefix` identities prove this
while the cursor remains below the old endpoint. Literal mask decomposition
then identifies the full new mask with the new state's own column plus the
mask of that proper border. The observer's diagonal and mask tests make both
parts clear. `trace_safe_reference` proves safety of the complete reference,
its exact cursor and its actual endpoint label.

`safe_reference_witness` translates that complete reverse reference to
`Basic.Witness`. It first proves every reversed finite slice follows the stated
original labels. Each forward cut therefore has its intended original state.
An ordered forward suffix-prefix match becomes a literal border of the
corresponding reversed prefix; base safety excludes the flagged pair.
Empty-suffix and diagonal comparisons are included, not removed as special
cases. `finish_implies_witness` follows.

For completeness, take a literal safe no-return completion C. A fresh prefix
whose failure parent is at least the old length would contain a full earlier
return, by the existing shifted-border lemma. Thus all fresh failure parents
are below the old length. Following C's actual letters and original states
constructs a trace with every required guard. This proves the converse of the
main equivalence. At maximal rank, another full return would increase rank,
so the checked rank result supplies precisely this no-return condition.

## 3. Correction to the earlier informal target

The earlier chat target "Finish iff any safe witness completion" was too broad.
This was an overstatement of the proposed interface, not a counterexample to
the repository's candidate, which uses Finish after the last rank milestone.

A four-state chain accepts exactly `010`:

```text
0 --0--> 1 --1--> 2 --0--> 3 (terminal final)
```

There are no Bad states or flags. The reversed reference `0`, with labels
`(3,2)`, has a valid complete witness extension `010`, but its Finish query is
false: reaching the original initial state requires returning to `0` at the
ultimate cut. The full reversed `010`, with labels `(3,2,1,0)`, does satisfy
Finish by an empty continuation. The regression is retained in the checker.

The checked equivalence keeps the no-return condition; the maximal-rank theorem
shows why that is the right interface for the proposed decision schema.

## 4. Validation and its limits

The two proof modules were built in a fresh target checkout and replayed through
`leanchecker`, using Lean 4.33.1, commit
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`. Ten unchanged imported source blobs
match the recorded a4e9dfc dependency hashes. The target build has 13 jobs.

All **62 named declarations/constructors, including 49 theorem declarations**,
were audited by `#print axioms`. Only the standard `propext` and `Quot.sound`,
plus `Classical.choice` in theorem proofs, are allowed. There are no custom,
unfinished-proof or native-evaluation axioms, and runtime definitions do not
use classical choice. The compile log has only an inherited unused-variable
warning in the unchanged `RankQueryFirstReturn` dependency.

The independent Python oracle tracks the SET of all matching proper-prefix
lengths rather than a longest-prefix cursor. It exhausts a finite graph of that
set and the original state. It imports no Python compiler or candidate evaluator.
On 180 deterministic cases, its 92 YES and 88 NO answers agree with native Lean
evaluation of the actual query. All 92 reconstructed positive words also pass
both an independently written literal witness check and native `witnessCheck`.
The corpus contains 179 safe references and one empty-reference boundary case;
negative oracle runs explore 113 states in total, so these are small tests, not
a claim of a difficult census. The full and compact outputs reproduce
byte-for-byte, including under a different Python hash seed.

These are finite-input regressions. The unbounded logical statements rely on
the Lean proof, not extrapolation from the corpus. NO is complete only for the
supplied fixed-reference no-return question.

### Local versus remote execution

Earlier Facts revision `dad7821` compiled and passed kernel replay remotely;
its obsolete audit rejected standard `propext`. The audit was corrected to the
repository's existing axiom policy and expanded to all named declarations.
Trace drafts subsequently required syntax and dependent-Fin repairs; those
failed revisions remain in branch history. No main theorem was weakened to
obtain the final proof.

At the inspected `b8da467` revision, all seven remote workflows failed before
executing steps. The underlying runner-start cause was not established. Local
validation then used the existing authorized one-day CI bootstrap of the
PUBLIC pinned Lean toolchain. Both downloaded artifact digests matched GitHub
metadata. No credentials, new toolchain version or decision oracle were used.
The bootstrap itself is not a research artifact and is not included here.

**The final proof evidence is local kernel execution, not a claimed green
remote run.** A complete repository test suite and integration into main were
not run locally; only the exact proof target, its dependency audits and the
native/independent finishing regressions were executed.

## 5. Reproduction

On a checkout containing these files and the repository's pinned toolchain:

```sh
cd lean
lake build +Subtail.RankQueryFinishTrace
lake env leanchecker Subtail.RankQueryFinishFacts
lake env leanchecker Subtail.RankQueryFinishTrace
cd ..
python3 experiments/check_finishing_trace.py --lean \
  --output /tmp/finishing.json --full-output /tmp/finishing-full.json
PYTHONHASHSEED=91 python3 experiments/check_finishing_trace.py --lean \
  --output /tmp/finishing-replay.json --full-output /tmp/finishing-full-replay.json
cmp /tmp/finishing.json /tmp/finishing-replay.json
cmp /tmp/finishing-full.json /tmp/finishing-full-replay.json
python3 - <<'PY'
import json
from pathlib import Path
saved = json.loads(Path('results/finishing-trace-semantics.json').read_text())
actual = json.loads(Path('/tmp/finishing.json').read_text())
assert actual == saved['native']
PY
```

The isolated workflow also generates the complete declaration/constructor audit.
Run Python with assertions enabled. Omitting `--lean` is explicitly reported as
Python-only evidence, not native Lean verification. Large full case outputs are
regenerated, not duplicated in Git.

## 6. Handoff and remaining obligations

This is an additive six-file contribution; the compiler, soundness, enumerator,
marks, shared imports and existing research records are unchanged. The branch
is published for coordinator integration, not force-merged into concurrent main.
After integration, import the new modules in the default build, rerun the target
and existing suite on the integrated revision, and update A018 and the tracker.

For stage 5, use `maximal_rank_completion_finishes` at the last reference of the
milestone decomposition, and `finish_implies_witness` in the reverse direction.
Connecting every arbitrary direct witness to that complete milestone chain,
proving the advertised quantitative shortening/product bound, and instantiating
the final decision schema remain separate obligations. The new
`safe_reference_witness` is a proved forward bridge; its arbitrary-witness
converse has not been separately formalized in this contribution.

The critical stage-4b semantic diagram-coverage theorem, the compiler clause
weight bound, the global F(k), and the remaining arbitrary-tree reduction/total
subtype decision are not established here. No candidate-status promotion or
independent human referee claim follows from this local finishing proof.
