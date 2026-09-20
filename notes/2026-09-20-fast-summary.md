# Proved finite saturation and practical entailment guards

Date: 2026-09-20. A010/A018, C081; coordination #55/#37.
Base: `c36096631acbd0c20bdcbaeec3245dc7e1679142`.
Status: Lean proof, kernel replay, source readback and native acceptance checks PASS.
The full diagnostic remains UNKNOWN because resource-capped cases are retained.
Source checkpoint: `cf125800a9c26cb4589d4eb0bd889d6a76b1a8e5`.

## Exact target and scope

For every finite expression input G and query s <= t, construct an executable
`EntailmentFast.entailsCheck` equal to the existing C081 Boolean. The value
domain remains arbitrary prefix-closed product-node trees. Keep the complete
reference procedure as fallback; a bounded shortcut never returns a negative
answer from failed search. This is a performance improvement, not a new
decidability or extension theorem. The reference Lean modules remain unchanged.

## Construction and ordinary proof route

1. For a push/pop/epsilon system on n controls, store a finite relation as an
   explicit table of pairs. Start with reflexive and epsilon pairs, then add
   compositions and matching push/balanced/pop pairs until stable. Every added
   pair is Balanced by its inductive constructors. At a fixed point the table
   satisfies all four closure rules, so `balanced_least` proves completeness.
   There are n*n pairs; strict growth cannot continue beyond that many pair
   additions. The implementation starts at the empty relation and runs at most
   n*n+1 rounds, stopping early when a round adds no pair. These rounds scan
   the finite carrier; this is not an event-driven queue implementation. The
   analogous finite graph closure replaces invariant-subset enumeration.
2. Cache the forward/reverse balanced tables. Evaluate supplied-word Pop and
   minimum-stack factorization using those tables. Replace control-graph path
   tests by finite graph closure. Prove exact equality with the old Pop,
   reachability, safety, satisfiability and supplied-address separation tests.
   This avoids both relation enumeration and recomputing its result at every
   use. The definitions must store finite data, not nested function closures.
3. Compute a sound positive relation over normalized variables. Its rules are
   reflexivity, listed inequalities, a denied variable below every variable,
   transitivity, and covariance between an upper-product premise and a
   lower-product premise. Soundness is induction on closure rounds using
   ordinary inclusion and `product_mono`. A fixed finite round budget and
   early fixed-point exit suffice: completeness of this shortcut is neither
   needed nor claimed.
4. Check exact supplied-address separation using the cached tables. Candidates
   are the seven binary words of length at most two and all addresses occurring
   in the input expression syntax. Thus a deep syntactic address can be tried
   without enumerating all words at that depth. A successful test has an
   arbitrary-tree countermodel by the existing separation theorem. Failure
   falls through; this candidate list is not a complete witness enumeration.
5. Return true after a sound positive proof or a failed exact satisfiability
   check; return false after a successful exact separation check; otherwise
   invoke the unchanged complete gated C081 Boolean. The branch proofs and
   reference correctness yield unconditional equality and correctness. Exact
   expression normalization transfers the result to the original input.

Each implication has its own checked Lean declaration, listed below. No claim that the shortcuts decide
all inputs, no finite-tree restriction, no classical choice in runtime and no
unchecked native replacement are permitted. The complete fallback establishes
termination even when the shortcut does not settle the query.

## Discriminating verification and measurements

Compare finite closure with the old exhaustive definition on small systems,
then use independent Python closure and explicit word/graph predicates on
larger selected systems. Include no controls where interfaces allow them,
empty words, epsilon cycles, matching versus mismatched push/pop, reverse
orientation, unsatisfiable denials, products, duplicated syntax and necessarily
infinite models. The ordinary proof review must inspect cached data use and
the actual runtime definitions separately from proof erasure.

Run matched E054 inputs on an isolated wb-marcus checkout under identical
20-second wall/CPU, 16-GiB Linux address-space and one-thread caps. Measure
phases and separate frontend from raw backend completion. Add generated
transitivity/covariance and deeper-separator families so an improvement is not
defined solely by the fixed corpus. Preserve every UNKNOWN and failed attempt.
The initial target was 26/26 full-expression cases. The measured result below meets it.

The current undecidability alternative is excluded only for C081's already
proved exact domain. Failure of this optimization would be a representation
or performance obstruction, not evidence that its semantics are undecidable.
The initial proof gate was a complete saturation proof and an equal cached
separation test. Both now pass; performance conclusions below use recorded execution.

## Proof and representation details

`StackSummaryFast.mem_balancedTable` gives both directions for every finite
control count and every system. Soundness follows from the four constructors
of `Balanced`. For completeness, every non-fixed round adds at least one pair;
`FiniteSearch.addNew` preserves membership, list order and absence of duplicates.
A duplicate-free list inside the n*n carrier cannot grow for n*n+1 rounds.
A fixed round is closed under reflexivity, epsilon, composition and a matching
push/pop around a previously balanced pair. The existing leastness theorem
then places every inductively balanced pair in the computed relation. This
bounds saturation rounds, not the height of a represented stack execution.

`CanonicalReachabilityFast.prepare` materializes three Boolean matrices:
forward balanced pairs, reverse-system balanced pairs, and finite path closure
in the reverse control graph. Reverse swaps push and pop as well as edge
orientation. The control graph combines reverse balanced edges with either
reverse pop letter, retaining the existing convention. Its path closure uses
`FiniteSearch.reachable`, with its full finite carrier, rather than the old
invariant-subset enumeration. `Correct` is a separate proposition, so runtime
cache construction does not carry a classical proof term into its dependencies.

For a supplied word, `popSet` folds one subset transition per letter, starting
with the balanced row. The proof uses the reference snoc transition theorem;
no stack-height cutoff is introduced. Reachability then enumerates every pair
of cuts of the supplied source and target words. Their remaining suffixes
must agree, and a common control must belong to the forward and reverse pop
sets. This is the existing exact minimum-height decomposition. Control reach,
denial safety, satisfiability and supplied-address separation follow by equal
replacement of their component tests. Prefix pop sets can still be recomputed
for different cuts; no optimal prefix-memoization claim is made.

The positive closure is deliberately a sufficient test. For the product rule,
constraints a <= l×r and l'×r' <= b, together with already established
l <= l' and r <= r', imply a <= b by covariance and transitivity. A denial
p <= bottom makes p <= q valid for every q. Every round is sound regardless
of the round budget; unlike balanced saturation, no completeness property of
this relation is needed. The cheap first rule test avoids building the full
closure for reflexivity, listed inequalities and explicit bottom sources.

For any finite candidate list, including the empty list, the final conditional
has three justified exits: a sound positive proof, an inconsistent premise
set (vacuous entailment), or an exact separating address (non-entailment).
All other cases invoke `TerminalDecisionLazy.rawNormalizedEntailsCheckLazy`.
Its unconditional correctness supplies the remaining branch. Normalization
then yields `EntailmentFast.entailsCheck_correct` over the original expressions
and `entailsCheck_eq` against the complete reference Boolean. There is no
caller satisfiability assumption and no restriction to finite or regular trees.

| Mathematical obligation | Checked declaration |
|---|---|
| Least balanced relation | `StackSummaryFast.mem_balancedTable` |
| Equality with exhaustive relation test | `StackSummaryFast.balancedCheck_eq_reference` |
| All three cached matrices are exact | `CanonicalReachabilityFast.prepare_correct` |
| Supplied-word pop and reachability | `popSet_eq`, `reachesCheck_eq`, `controlReachCheck_eq` in `CanonicalReachabilityFast` |
| Exact denial and separating-address tests | `satCheck_eq`, `separationCheck_eq` in `CanonicalReachabilityFast` |
| Positive relation is sound | `EntailmentFast.positiveCheck_sound` |
| Any finite candidate list preserves the decision | `EntailmentFast.normalizedWithPaths_correct` |
| Original-expression semantics and reference equality | `EntailmentFast.entailsCheck_correct`, `entailsCheck_eq` |

## Limits and next question

The complete fallback still constructs the old summary space and rank-query
machinery. This change does not optimize all 4^n summary states or replace
all calls inside that fallback. The raw diagnostic deliberately calls the
unchanged backend to keep that cost visible. The small Python countermodel
library is also unchanged and remains an incomplete explanation search.
The caller's timeout still returns UNKNOWN, never an inferred answer.

The next performance investigation should profile positive closure, transition
predicates, balanced saturation and supplied-path checking on the deeper
full-expression family. Materializing the five transition matrices and using
a queue for changed pairs are specific candidate improvements; their gains
are not yet measured or proved. Constructing only reachable summary states
with a proved language/flag correspondence remains a separate backend task.
Complete finite-countermodel extraction is also still open as an executable
feature. No conclusion about a tight complexity class,
explicit-top extension, or the open original C080 F follows from this work.

## Reproduction and verification boundaries

Use the pinned Lean 4.33.1 toolchain. The optional solver modules are built
explicitly; they do not change the default reference import graph.

```sh
(cd lean && lake build +Subtail.EntailmentFast)
(cd lean && lake env leanchecker Subtail.EntailmentFast)
python3 scripts/check_fast_summary.py --output tmp/fast-summary-axioms.json
python3 scripts/check_lean.py
python3 -m unittest discover -s scripts -p test_subtail.py
python3 scripts/subtail.py examples/entailment/premise.json --timeout 20
python3 scripts/subtail.py examples/entailment/reverse.json --timeout 20
python3 scripts/subtail.py examples/entailment/zero-spine.json --timeout 20
```

At `cf125800a9c26cb4589d4eb0bd889d6a76b1a8e5`, the isolated wb-marcus checkout
passed the default core check, optional solver build, imported-module kernel
replay and all 97 named declaration dependency closures. The 45 non-theorem
declarations contain no transitive `Classical.choice` dependency. The audit
also rejects unfinished proofs, custom axioms, noncomputable or unsafe code,
and unchecked runtime substitutions in the three new modules. Source scanning
and dependency checks complement, rather than replace, semantic readback.

The unchanged 16 Python boundary tests passed locally. Actual wb CLI runs
returned ENTAILED for `premise.json` and NOT_ENTAILED for `reverse.json` and
`zero-spine.json`; both negative examples returned graphs checked by the
separate Python certificate predicate. That predicate and the parser/launcher
remain outside the Lean proof. These smoke checks do not establish extraction
completeness or authorize treating an unsuccessful explanation search as a
positive decision.

## Validation-driver corrections preserved

The first driver draft was not accepted as evidence. Parent review corrected
its multi-marker handling, baseline/candidate count grouping, the reference
rendering API call, and source-hash coverage. Review also found an orientation
error in the independent oracle for the reverse control-path matrix: its
entry (p,q) must be compared with original-system reachability from (q,[])
to control p with arbitrary stack. For one push edge 0 -> 1, the entry (1,0)
is true, whereas a reverse-system run starting on an empty stack cannot pop.
That literal case checks the repaired oracle direction.

The first pinned native harness run at `21c5d76` failed before executing any
probe because a caller-supplied relative scratch path was interpreted from
Lean's working directory. It correctly reported FAIL, not a mathematical
answer. Resolving probe paths to absolute paths repairs this boundary at
`9a866c1`. The new generated family also calls the full expression frontend
on nested products; supplied-address component tests alone do not cover the
syntax-guided candidate list. No mathematical source changed for these repairs.

## Measured result: E055

[Combined receipt](../results/entailment-fast.json). Native source checkpoint:
`9a866c196f30f2fe1f11d4201d6237642fbd3cb8`, wb-marcus. The Lean source is identical
to the proof-checked `cf12580` checkpoint. Fresh baseline and candidate runs use
the same 38 fixtures, machine and 20-second wall/CPU, 16-GiB Linux address-space,
one-thread and 32768-KiB stack limits. Query timing includes Lean startup but
excludes the initial module build.

| Entry point | Previous gated version | Cached version |
|---|---:|---:|
| Full original expressions | 17/26 PASS; 9 UNKNOWN | 26/26 PASS |
| Normalized wrapper | 5/5 PASS | 5/5 PASS |
| Direct raw backend | 2/7 PASS; 5 UNKNOWN | 2/7 PASS; 5 UNKNOWN |
| Total | 24/38 PASS; 14 UNKNOWN | 33/38 PASS; 5 UNKNOWN |

No completed answer is wrong and no previously completed case regresses.
The 26 candidate frontend calls take 0.668–0.771 seconds each. The raw calls
are intentionally identical in both variants: they expose the unchanged
backend cost and do not exercise the new frontend shortcuts. The old E052
Mac and E054 receipts remain unchanged historical records.

The independent P-automaton oracle agrees with five aggregate Boolean vectors
across 62 small systems: forward/reverse balanced, reverse control paths,
arbitrary supplied-stack reachability, and control reachability. Vectors are
compared by their lengths and two rolling digests, so this is regression
evidence, not a new all-input proof. The six normalized SAT/separation vectors
use an exact integer encoding. Both component phases PASS within the cap.
The ordinary source readback and Lean equalities supply the semantic proofs.

Generated families complete 16/19 cases: transitive chains through ten controls,
covariance chains through fifteen controls, supplied paths through depth eight,
and full-expression nested products at depths three and four. The last two
take 3.977 and 12.501 seconds. Supplied separation at depth twelve and full
expressions at depths six and eight exceed twenty seconds and remain UNKNOWN.
The full-expression negative family has an explicit finite countermodel:
set x to product(bottom,bottom) and y to bottom, then put d identical left
product contexts around each. Their first separating address is d zeroes.
This exercises candidate paths beyond the fixed seven short words.

No peak-memory or per-algorithm-phase profile was measured. The next measured
question is where the deeper cases spend their time; the data do not yet
justify choosing between transition-table caching, a more efficient saturation
queue, and prefix-result reuse. The unchanged full summary construction is
another independent cost. Passing the basic target establishes a useful
initial interface, not broad practical scalability.

```sh
python3 experiments/check_fast_summary.py --components \
  --output tmp/fast-components.json --scratch tmp/fast-components
python3 experiments/check_fast_summary.py --benchmark --compare-baseline --generated \
  --output tmp/entailment-fast.json --scratch tmp/entailment-fast
```

CI builds and kernel-checks the new modules, audits their runtime dependencies,
checks the independent components and enforces 26/26 frontend plus 5/5 normalized
completion. Raw and larger generated limits stay visible; wrong answers and
compilation errors fail the diagnostic. The original reference checks remain.

## Diagnostic interruption follow-up

At `6163f27ea0d0964fadc747a82c2dceff287fc5d2`, a targeted Python fix makes a process killed by a signal
remain UNKNOWN even when no error message is printed. Explicit compiler
errors still fail. The 17-test boundary suite passes, including CPU-limit,
kill and interruption outcomes. Replaying all 97 recorded native process
outcomes through the corrected classifier changes none of their statuses.
This replay is not a new Lean run. All native timing/answer receipts remain
pinned at `9a866c1`; the five-line classifier change does not modify a Lean
query, source definition or proof. The combined receipt records both source
versions and their validation separately.

## CI build-order follow-up

The first published CI run,
[35484509265](https://github.com/mhenglein/subtail/actions/runs/35484509265),
failed before the new solver checks. An existing `Stack*.lean` audit found
`StackSummaryFast.lean`, but its optional module had not yet been built. Lean
reported that `StackSummaryFast.olean` did not exist. No theorem check or native
answer failed at this point.

The workflow now builds `StackSummaryFast` in its early explicit module list,
before that wildcard audit. Running the affected build and audit commands on
the owned wb-marcus checkout passes all 145 declaration closures; an owned
scratch path replaces the CI runner's temporary output path. Workflow ordering
and YAML validation pass. This changes only build order and this note; all
mathematical source, proofs and native receipts remain at their stated pins.
The replacement main-run status is recorded in issue #55 rather than inferred
from the old failed job.
