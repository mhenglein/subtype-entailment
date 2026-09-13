# Source-sensitive target-return elimination

Date: 2026-09-13. Base `b79bc02d5a669fde60484a463941b16e03805050`.
Workstream A017; C079 / E051. Q004 and unrestricted Problem 1.7 stay OPEN.

**WRITTEN PROOF + REPRO. Independent mathematical review pending, not Lean.**

[Full proof, all hypotheses and counterexamples](../notes/2026-09-13-target-return-elimination.md).
[Initial route and recorded outcome](../notes/2026-09-13-target-return-route.md).
This replaces last-target UNIQUENESS with source-sensitive checks at the last
occurrence of each certified original target label. Legal repeated suffixes
are retained in one shared full candidate word. The period lemma, original
boundary normalization and direct/reversed predicates are prior C036-C038 and
C077/C078 dependencies; their evidence is not independently re-certified here.

## Claim

<a id="c079"></a>

### C079 — Native elimination for productive return-closed target columns

**Statement.** In a normalized binary terminal k-state input, let r be the
number of original flag-target labels. For each target t, form the productive
nonmerging synchronized pair graph rooted at its incoming flags. Require that
every reachable pair whose right original label returns to t still belongs
to that incoming flag column. This is the return-closure certificate (RC).
If all columns satisfy (RC), witness existence is decidable by the native
algorithm below; every positive input has a witness of length at most
`2*k^(2^r)` for k>=2. The one-state case is direct. No sharpness is claimed.

**Mechanism.** (RC) transports an earlier bad comparison to the last occurrence
of its target label, including overlapping copies. It is inherited by regular
restrictions with a transition-preserving projection to the preceding domain.
A productive target-free accepting tail cycle gives YES by C077. Otherwise
all possible last-target tails are finite and have length at most K-1 in the
current K-state domain. For a supplied tail Y of length m, an exact filter
retains the designated terminal occurrence and forbids other occurrences only
at original sources forbidden into its target. It needs at most K*m+1 states:
store the longest matching proper prefix and its starting domain state.
Every smaller matching suffix's start is determined by propagation.

After filtering, certify (RC), remove the WHOLE original target column and
recurse on the same full words. Original labels, not product-state copies,
decrease. At most r levels occur; child state counts are at most K^2. The
bound follows by induction without appending independent prefix pieces.

**Scope and limitations.** The implementation also checks closure after
filtering, which can certify additional instances. Failed return certificates,
resource caps and host recursion exhaustion are UNKNOWN. All negative branches
must be covered by finite proofs. There is no complete coverage theorem for
arbitrary flags, no general complexity membership, and no unrestricted subtype
solution. The single-negated-containment literature is not a decision dependency.
[Exact definitions and proof](../notes/2026-09-13-target-return-elimination.md).

**Discriminating examples.** A five-state nonflat SCC with three sources and
three targets has witnesses but NO accepted word with a unique last-target
suffix. The old target-anchor wrapper returns UNKNOWN; this solver returns
`0100` through three eliminations (the shortest witness is `00`). An eight-state
negative example gets a complete recursive NO certificate, also beyond that
wrapper. This is not a claim of separation from every older restricted solver.

**Preserved obstruction.** The existing (2,3) modular input admits
`111101111110`, which passes all last-per-target tests but violates the flag
at cuts (0,7), states (0,5). Its synchronized `111` return reaches (1,5), which
is not flagged. Thus dropping (RC) is unsound. This positive input and the
six-state marking-barrier negative input both remain UNKNOWN for this method.
Splitting product copies of an original target is separately refuted by the
labeled-domain regression. C073-C078 and Q004 keep their prior scope/status.

## Experiment

<a id="e051"></a>

### E051 — Shared-word filters, target elimination and independent NO replay

**Commands.** Python 3.10+, standard library only, from the repository root:

```sh
python3 experiments/check_target_return.py --output /tmp/target-return.json --full-output /tmp/target-return-full.json
cmp results/target-return.json /tmp/target-return.json
python3 experiments/target_return.py examples/target_return/legal_repeats.json
python3 experiments/target_return.py examples/target_return/recursive_no.json --output /tmp/target-return-no.json
python3 experiments/check_target_return.py --verify-instance examples/target_return/recursive_no.json --verify-certificate /tmp/target-return-no.json
python3 experiments/target_return.py examples/target_return/modular_unknown.json --uncapped
```

[Solver](../experiments/target_return.py),
[independent filter/certificate checker](../experiments/check_target_return.py),
[compact reproducible results](../results/target-return.json).
The full output regenerates all five named fixture proof trees, original
inputs, witnesses and pair certificates; no chat attachment or network is needed.
The preceding `target_anchor.py` dependency remains byte-for-byte unchanged.

**Coverage.** Seed 20260913651. All 1,024 three-state inputs give 564 YES and
460 NO, agreeing with the previous complete checks. Other corpora include 120
complete acyclic languages, 120 exact filter-language equivalence products,
30,600 literal filter-word checks, 64,512 three-state word checks and 113,442
last-column comparisons on certified inputs. Of 248 additional productive
random inputs, 222 are initially return-closed and all finish at the supplied
caps. The dynamic outcomes are 232 YES,11 NO,5 UNKNOWN. No bounded scan supplies
NO, and no claim about untested inputs is inferred from these counts.

**Negative verification.** 536 proof replays include 501 boundary-empty slices;
these are NOT advertised as 536 difficult recursive proofs. The checker visits
41 nonempty negative nodes, proves equality of 43 filter languages against a
literal-window automaton, and verifies three nontrivial return eliminations.
It recomputes productive pair sets, verifies closed reachable sets and exact
finite-tail coverage, and recursively checks every negative branch. It does
not invoke the new solver to decide a negative node. Missing-tail and corrupted-
closure certificates are rejected. Explicit overlap, original-label grouping,
invalid-cap and UNKNOWN-cap regressions are included.

**Evidence level.** Deterministic compact and full output replay passed locally.
These are finite implementation/certificate checks, not a mathematical referee
or Lean formalization. No full local repository suite was run. The dedicated
read-only workflow checks the integrated research index and reproduction;
read its remote status before claiming success.

## Handoff

Audit the projection hypothesis, longest-prefix start-state filter, grouped
original labels, overlap transport, and complete branch inventory. Then attack
return-loss branches with an exact existence-preserving treatment or a complete
finite cover. Passing last-per-target checks without that argument is unsound.
The new theorem discharges simultaneous synthesis for the return-closed class,
not the unresolved unrestricted coverage implication. Existing ownership and
execution statuses are unchanged; no additional agents were launched.
