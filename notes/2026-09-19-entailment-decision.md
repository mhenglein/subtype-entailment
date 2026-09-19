# Complete expression-level entailment decision: proof and validation

Date / author: 2026-09-19, Codex Astra entailment-completion-20260919.
Approaches: A010/A013/A018; claims: C081, C029/C031; native regressions: E052.
Base: e21c599388e32e3d024f3efcde9e3500e838bdcd.
Status: complete Lean proof and independent semantic readback; exact validation
and execution limits below. This qualitative result is separate from C080's
proposed quantitative U/F estimates.

## Exact theorem and semantics

For every natural n, finite list G of pairs of finite expressions over Fin n,
bottom and one covariant binary product, and two such expressions s,t:

```lean
Subtail.EntailmentDecision.entailsCheck_correct
  (G : Input n) (s t : Expr n) :
  entailsCheck G s t = true ↔ ExprEntails G s t
```

`entailsCheck` is a total executable Bool. `ExprEntails` quantifies over every
valuation into `TreeSemantics.Tree`: arbitrary prefix-closed product-node
sets, including infinite and nonregular trees. The premises are exactly G;
the queried inequality is not added as a premise. The direction is the
inclusion of the interpretation of s into the interpretation of t.
There is no satisfiability, finite-model, regular-model, witness-bound, C030,
U/F or caller-supplied absorption premise.

The memo's finite named constraint set and variable query embed by indexing
the finitely many names with Fin n and listing the constraints. Duplicate
premises do not affect universal satisfaction. This effective finite input
encoding is ordinary mathematics; no theorem about parsing arbitrary text or
JSON is claimed. The inherited TreeSemantics path-set/diagram correspondence
uses the precise arbitrary-tree domain. The final source review re-read that
boundary rather than replacing it with a finite-tree test semantics.

## Finite constructions and complete argument

1. **Normalize syntax.** Collect finite product occurrences and used bottom
   from premises and query. A Naming has n+P+B variables; old variables keep
   their indices. Both product inequalities fix each new product slot, even
   with duplicate syntax. A denial fixes the bottom slot. The total finite
   definitions plus original clauses form `normalized G s t`.
   `normalize_entails_iff` proves original `ExprEntails` iff normalized
   `Entails`: every original model extends, every normalized model restricts,
   and the queried meanings and separating address are preserved. Query-only
   syntax, n=0 constants, UNSAT and infinite valuations are covered.
2. **Construct one summary instance.** For normalized C and variables a,b,
   bind I=`SummaryAutomaton.summaryInstance C a b`. Its state set enumerates
   pairs B,A of control subsets; the alphabet is Bool. Its canonical initial
   pair and total finite tables use exact last-letter Pop transitions.
   Finals exclude forced roots. Bad states combine the exact UNSAT bit and
   prefix-denial danger. Ordered flags are B(left) intersect A(right).
   `not_entails_iff_witness` characterizes arbitrary-tree non-entailment by
   original Witness in I. `summary_absorbing C a b` proves strong absorption
   for every state, including unreachable states.
3. **Split the unchanged witness problem.** For that same I,
   `SubtypeTerminalBridge.not_entails_iff_infinite_or_terminal` equates
   non-entailment to `InfWitness I` or a positive terminal decision on
   `terminalize I`. Terminalization removes unsafe edges before selecting
   safe original final sinks; flags, Bad and initial state are preserved.
   InfWitness retains an original witness and an explicit safe finite stem
   with a nonempty safe cycle. Empty/diagonal cuts remain present.
4. **Decide both branches.** `InfiniteDecision.infiniteWitnessCheck_correct`
   applies using the proved all-state absorption of the same I. It uses
   finite bounded-cycle enumeration and a complete finite reverse monitor
   over all prefixes; no prefix-length cutoff is assumed.
   `RankQueryDecision.terminalWitnessCheck_correct` applies to the terminal
   instance. Its finite compiler needs no numerical clause-weight contract
   or explicit F(k). Thus normalized non-entailment is exactly the Boolean
   OR of these two total checks.
5. **Negate and compose.** `rawNormalizedEntailsCheck` negates this OR.
   `rawNormalizedEntailsCheck_correct` follows by the four Boolean cases.
   `normalizedEntailsCheck` adds only separately proved cheap cases:
   reflexivity, an actual leq premise, UNSAT vacuity, or an empty-address
   countermodel. A failed empty-address test falls through to the complete
   raw backend. `entailsCheck` applies this normalized check to the exact
   normalized query references. `entailsCheck_correct` composes its iff with
   the reverse of `normalize_entails_iff`. `entailsCheck_false_iff` records
   the equivalent negative-answer theorem.

Each algorithm is a terminating Lean definition on finite data. Classical
reasoning in erased correctness proofs does not supply executable choices;
the complete imported dependency closures of the runtime definitions are
audited separately. Neither a caller-provided hypothesis nor a test timeout
supplies an answer. No construction or source definition from the earlier
semantic or branch proofs was weakened for this composition.

## Independent semantic review

The separate entailment_review session read the final source at
`9f7d57cbd695a68dd52a69dc81b8446bd7c85d9e` and its exact definitions. It found
no blocker in arbitrary-tree quantification, input syntax, inequality
direction, exclusion of the query from premises, model transfer, the single
shared I, strong absorption, original-final terminalization or the guard
proofs. [Full readback](2026-09-19-entailment-decision-independent-readback.md),
original review commit `5803e361a3f2aeb40fda91fe3aeb66c4e6d2abc0`.

That reviewer did not run builds or native checks. Those are the separate
executed author/worker gates below. It inherited the previous normalization
and C029 readbacks and is not a blind derivation or human referee report.
Review notes retain the validation status when written rather than having
later runs silently attributed to their reviewer.

## Q004: an ordinary computability corollary

For k>=1 there are exactly `k*(k+1)^(2*k)*2^(2*k+k*k)` labelled `Instance k`
tables: initial state, two partial transitions per state, final/Bad bits and
ordered flag bits. Enumerate them effectively and test TerminalFinals by
checking every final state and letter. Classify each terminal instance with
`terminalWitnessCheck`. For every YES instance, enumerate finite binary words
by length then lexicographic order until `witnessCheck I w` succeeds.
`terminalWitnessCheck_correct` guarantees such a word exists, and
`witnessCheck_correct` gives its effective recognition. Each search terminates;
there are finitely many searches. Take the maximum `|w|+1`, default 0, as R(k).
Set R(0)=0 because `Instance 0` would require an impossible `initial : Fin 0`.

A word w has `|w|+1` run positions, so its source visits are bounded by this R.
Relabelling a k-state carrier preserves all fields and visits; enumerating
labelled copies only repeats equivalent inputs. This proves exactly the
existential total-computability statement in [Q004](../research/conjectures/Q004.md).
The separate reviewer checked this corollary and the actual terminal theorem's
hypotheses in a follow-up read-only pass and confirmed it, including k=0,
effectiveness and representation. Its conclusion is recorded in the
[coordination handoff](https://github.com/mhenglein/subtail/issues/37#issuecomment-5745427824).

This is an ordinary proof, not a new Lean declaration or implemented R.
It gives no practical bound, closed formula, C080's particular F, C030
realization or decision for arbitrary nonterminal/nonabsorbing instances.
The earlier Q004 lower bounds and failed local transformations remain valid.

## Source provenance

Normalization contributors were integrated from the exact released heads:

- #49:`d85e203e0d96bb5b452c89a4b06a6cc772195320` — Lean normalizer, audit and
  literal original-syntax checks.
- #50:`7b9ea558ad54753cd09af3e8dfa22bb45503735c` — distinct Python reference
  and its own tests. Its allocation order differs; evidence is not transferred
  between the two implementations.
- #52:`6ed3cfaf9906e6207de7b8c8dfc9753f40338a51` — normalization readback.

The conceptual outline preceded composition at `23165f884fc295f04973189b55e78f068de44b41`.
Final proof/runtime source: `9f7d57cbd695a68dd52a69dc81b8446bd7c85d9e`.
Audit and consolidated workflow: `56abb538e999954f6ed0dce067e3498777e51ab8`.
All later record/review changes preserve these proof files. Their SHA-256:

| Source | SHA-256 |
|---|---|
| EntailmentDecision.lean | `a899b12e1d2b968053a0062a1600c9d368fe5c16f1ba3b74aef591b311088f59` |
| ExpressionNormalization.lean | `6e69fa21ebf0a0ffa65f78c976eb6681a85e9c9778cf96e57d16fb86b1285b82` |
| TreeSemantics.lean | `8b08b74d08bac48454f99f0241eb066ef6b218334641f284bc26423957a78f2e` |
| SubtypeTerminalBridge.lean | `4a6fb1e783fdf052c1ac61bfd24aae9dbc5d1c441961e41d7cd02f434d57b751` |
| InfiniteDecision.lean | `d9679db4b52062a707f74c4a7198137f608660930e3f4a2d868ab4efac40228d` |
| RankQueryDecision.lean | `51fef747bb443d313559e57d8fb8e3c1ce68b804eb4883a7d504e2945da5bd8a` |

## Executed validation

On wb-marcus, Lean 4.33.1 and Python 3.13.14, at the final proof source above
with audit/workflow 56abb53:

| Command / check | Outcome and exact scope |
|---|---|
| `python3 scripts/check_lean.py` | PASS: full default build, whole-library kernel replay, earlier core audits/native regressions; saved legacy result unchanged |
| `lake -d lean build Subtail.ExpressionNormalizationAudit` | PASS: separate native audit executable and imported normalizer |
| `cd lean && lake env leanchecker Subtail.ExpressionNormalizationAudit` | PASS: kernel replay of the separately built audit module |
| `python3 scripts/check_entailment_decision.py` | PASS: 91 complete named transitive dependency closures, 39 non-theorems; no classical choice in executable definitions |
| Native ExpressionNormalizationAudit output checked by `experiments/check_expression_normalization_lean.py` | PASS: 372 native outputs; 567340 extended finite valuations, 7624 original valuations, 10479 exact query comparisons and adversarial guards |
| `python3 experiments/check_expression_normalization.py` | PASS: 1352 exhaustive syntax inputs, 250 seeded inputs, 10600 original-extension checks, 115340 normalized valuations, 38936 address checks, 10000 nested-product stress, 14 malformed inputs, 9 adversarial groups, 3 CLI roundtrips |

Fresh normalization mathematical counts, source identities and mutation guards
were compared to their own saved records. Environment metadata remains the
historical run's metadata; it is not claimed to match a different host.
The finite normalization valuations are regression evidence only; the model
extension/restriction theorem quantifies over arbitrary infinite valuations.
Both suites are retained in the consolidated dependency-triggered Lean workflow.

The real wb-marcus Lean MCP returned the open goal for the optional
false-answer corollary and checked an isolated successful proof step. A direct
rewrite initially failed under negation; `not_congr` with
`Bool.eq_false_iff` solved it without changing the statement. This exercised
the interactive tooling against the pinned project rather than a toy proof.

Native full-frontend coverage, exact completed comparisons and resource caps
are recorded under [E052](../experiments/README.md#e052) and in its saved JSON.
A backend timeout is UNKNOWN, even if an independent proof establishes the
fixture's expected answer. No bounded model census establishes universal
positive entailment. Earlier branch-specific exhaustive native results remain
at their original recorded revisions: their all-state correctness comes from
the checked theorems, not the number of agreeing tests.

The source tree and reviews were preserved when wb-marcus became unreachable
after these checks. Parent integration continued in a separate Mac checkout
from pushed 56abb53 plus the original review commit. No remote checkout was
reset or overwritten. Final combined checks, published main revision and CI
links are recorded in #31/#37; branch pushes with no matching workflow trigger
are not described as CI passes.

## Limits and next question

The mathematical objective is qualitative decidability. The current backend
can be enormous: a normalized n-variable summary has `4^n` physical states,
and its branch algorithms deliberately use complete finite enumerations.
Even a simple bottom-left query may exceed the 20-second native test cap.
The guard cases improve common examples but do not claim useful complexity.

C080's explicit U/F estimates and separate C030 converse certification remain
outside this contribution. Unrestricted nonabsorbing abstract BorderAvoid,
other constructors and finite-tree entailment are different targets. The
unavailable original analysis-2026 archive remains retired as a task.

The next useful investigation is a readable end-to-end mathematical account,
careful comparison with prior work, or a specific proved runtime improvement.
None is automatically assigned by this handoff. A theorem count or green CI
is not a substitute for the exact proof and semantic readbacks above.

## Final integration checks and review follow-up

The separate final records review found no mathematical overclaim in C081 or
Q004. It requested fresh generated navigation and explicit historical wording
in the older Q004 sections; the final record pass applies both. That review
was read-only and did not run Lean or native tests.

After the workbench connection failed, the Mac integration checkout at
`78c7d587731eaa8dcce8b0226113fb494d038857` independently passed
`python3 scripts/check_lean.py`, the separate ExpressionNormalizationAudit
build, the 91-declaration audit and unchanged legacy-result comparison, using
Lean 4.33.1. Mathematical sources match the pinned hashes above. Documentation
updates were uncommitted during these checks and did not affect the build.
The 13 navigation tests and 9 prior-work retrieval tests also passed.

The native worker released its original uncommitted corpus and partial guard
record explicitly. Parent resumed it in the local isolated checkout, retained
the independent fixture justifications, and added whole-process-group timeout
cleanup, explicit entrypoint coverage and strict smoke execution. The complete
native run's checker source is `e867092`; its mathematical source is still
9f7d57c. [Scope and provenance](https://github.com/mhenglein/subtail/issues/31#issuecomment-5745474531).
The consolidated CI runs the completed smoke cases strictly and compares their
answers/source identities with the saved full diagnostic run. Expensive
UNKNOWN probes are preserved as diagnostic evidence and are not made into
required passing cases or negative answers.

Final native evidence (Mac, Lean 4.33.1, checker e867092): 38 cases attempted,
25 completed and agreed (17 full-expression, 5 guarded normalized, 3 direct raw),
13 UNKNOWN timeouts, 0 mismatches and 0 NOT RUN. All three completed raw calls
returned false; the raw true-answer probes did not complete within 20 seconds.
The overall full diagnostic status is UNKNOWN. The 17 smoke cases separately
passed strict replay and the exact CI answer/source comparison.

Final record validation passes `scripts/research_index.py --check`, the 13
index tests, `notes/prior-work/search.py --check`, the 9 retrieval tests and
`git diff --check`. The original core `experiments/run_experiments.py` also
passed locally with no saved-result change. The separate normalization audit
module passed fresh local kernel replay. The obsolete isolated-workflow link
was repaired by preserving its historical pinned source and linking its
consolidated replacement. No mathematical definition changed during this pass.
