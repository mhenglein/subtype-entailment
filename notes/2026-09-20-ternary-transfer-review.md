# Ternary transfer: adversarial readback and review boundary

Date: 2026-09-20. Author/session: ternary-transfer-20260920.
Base: 19b06d4fed9da635d9b911f0e908d04e4fc4b099.
Scope: [ordinary proof](2026-09-20-ternary-transfer.md), isolated checker and receipt.

## Status: independent mathematical review PENDING

This is the author's adversarial readback plus independent-ALGORITHM evidence.
It is NOT an independent agent/human review. No second reviewer was launched
or claimed to have approved the theorem. A precise read-only review request
was posted in #72, comment 5750385093. No affirmative review was received at
this checkpoint. This limitation blocks promotion to independently reviewed
or Lean-checked status, not the presentation of an ordinary proof attempt.

## Critical statement audit

The proposed theorem is a total COMPUTABLE, query-dependent many-one
reduction. It is not a polynomial syntactic encoding or a valuation-wise
isomorphism. Its preprocessor uses the existing binary C029 function; its
terminal output is C030's literal constraint realization. No ternary decision
is presupposed. The output-size bound does not bound this preprocessing.

The source uses constructor-address sets with bottom empty and one ternary
covariant constructor. Arbitrary infinite and nonregular values are included.
There is no explicit top, second label or reversed argument. Normalization
uses one shared valuation; query-only definitions are conservative, and the
query itself is not added as a premise.

The SAT guard is essential. With controls a,b,d, a forced constructor at d and
a denial d<=bottom, the source is inconsistent while the summary for a<=b can
accept epsilon. The proof's semantic summary equivalence explicitly assumes
source SAT. The test compares canonical separation with SAT AND Witness and
preserves this disconnected-denial regression.

The full physical subset-pair summary is strongly absorbing, including
unreachable states: finality excludes every forced control from the reverse
Pop pre-closure, so the next reverse component is empty. This proves both
finality and an empty incoming flag column, the exact binary C029 hypothesis.

Intermediate binary states must inherit original finality, but must also be
Bad if they have no safe leaf completion. Finality alone could introduce
uncompletable witnesses; nonfinal intermediates violate strong absorption.
Only boundary/boundary pairs carry flags. Complete prefix-code words preserve
every ordered suffix-prefix test. An incomplete witness is completed, not
truncated. A separate explicit fixture tests that distinction.

The final C030 target admits unrestricted binary auxiliary valuations. A
separating address from ANY target model yields a terminal witness by C030,
then a coded/source witness, then one canonical source valuation satisfying
ALL original premises. No encoded-image assumption enters this direction.
The maps on all premise models are completed using baseline models; they are
not claimed to preserve query truth on all non-countermodels.

No finite-valued transfer follows: C030's lower-copy baseline and canonical
reconstructions can be infinite. Infinite graph tests use exact finite pair
reachability, not a depth cutoff. The original source value need not be
regular; canonical replacement obtains regularity from finite seed NFAs.

## Executed evidence

Command, in the isolated partial workspace:

    python3 experiments/ternary_transfer.py --output results/ternary-transfer.json

The [receipt](../results/ternary-transfer.json) records source hash, seed,
Python/platform and elapsed time. All assertions passed:

- 488 absorbing instances; 39,136 complete-word coding comparisons;
  124,440 binary words; 16,422 binary witnesses, of which 5,358 required
  safe completion. One-state arities 1--4 are exhaustive; the larger cases
  are seeded samples, not a complete census.
- 70 SAT comparisons and 2,467 word comparisons against a separately
  implemented Post* epsilon-NFA saturation; 448 extracted regular
  countermodels checked by all-depth graph inclusion; 1,936 full physical
  states checked for strong absorption.
- 61 terminal binary instances, 1,891 exact C030 word/model comparisons,
  61 satisfiable baseline graphs and 23 countermodel graphs. Three realized
  countermodels also decode through the ternary coding layer.
- Nine original-expression/infinite-graph fixtures, including non-root
  separating addresses 0,1,22, bottom-valued auxiliaries and query-only names.
- The full untrimmed pipeline fixture has 3 normalized source names, 64
  ternary states, 128 binary states, 257 output variables and 2,697 output
  constraints. Its output graph passes every generated premise and separates
  the query. The left query value has a root but no node at address 1, so it
  is outside the naive ternary encoding's image. It maps back to a source
  countermodel of y<=T(bottom,bottom,bottom) / y<=bottom.
- Both fixed branches are exercised: source inconsistency and a literal
  witness/stem/cycle for the positive infinite branch. The terminal fixture's
  negative infinite branch has an independent safe-initial-sink proof.
  These fixture-specific certificates are NOT execution of C029.
- The failed homomorphic encoding is checked on all nine source values under
  its finite upper bound. Three binary nodes are minimal for that instance.

The independent NFA algorithm does not use the balanced/minimum-stack summary
being tested. It still shares the source normalization and is implemented by
the same author. Software differential checks cannot replace a separate
mathematical review of the all-input proof.

## Preserved failed trials and repairs

The original homomorphic encoding is mathematically refuted, not deleted.
A nontruncation test was initially written with source first letter 1 and
binary partial word 101. Literal Witness correctly rejected it: the suffix
comparison still conflicted. The fixture was corrected to first letter 0,
partial word 01 and completion 010. No encoding definition was changed by
that test repair. The first failed log is not a result of the final suite;
the relevant counterexample and explanation are retained here and in JSON.

An unconditional summary/model comparison would silently omit forced-denial
vacuity. The script explicitly includes SAT in that equivalence and has a
separate regression showing why. This is not evidence that C081 is false.
Making intermediate states nonfinal is preserved as an executable mutation
that violates the exact strong-absorption predicate.

## Not executed and next acceptance obligation

No Lean or Lake is installed in this container. Direct GitHub DNS/git access
is unavailable; the source was inspected with the authenticated connector.
The local Git worktree has a labelled synthetic partial-workspace base, not
an upstream checkout. No default build, kernel replay, full repository test
suite, C029 native call or checked generic-arity theorem was executed here.
The existing pinned binary proof receipts are inherited evidence, not fresh
validation of this addition. The isolated script is a component checker, not
a complete command-line frontend calling the binary C029 executable.

A useful next independent review should first read Sections 3--7 of the proof
against Basic.Witness, AbsorbingTerminal.Absorbing/c031 and C030. The selective
Lean target is absorption-preserving coding plus safe completion; a later
full theorem must also certify normalization, the generic canonical bridge,
SAT and case composition. No existing Lean definition should be changed to
make the new statements easier.
