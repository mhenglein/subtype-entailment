# Formalizing the rank-query candidate in Lean

Date: 2026-09-18. Base main: `9e9d3ecfe1277bd6e7ea6aeffdf035c12e477f89`.
Workstream A018 supporting A017. This branch is an initial formalization,
not a formal proof of unrestricted subtype entailment and not a claim-status
promotion. [Initial route](2026-09-18-lean-rank-route.md).

## Delivered and checked

[TerminalRank.lean](../lean/Subtail/TerminalRank.lean) reuses `Subtail.Instance`,
`runFrom`, `runFrom_append`, and `Agrees`. It does not redefine witnesshood or
introduce a new tree semantics. The pinned toolchain is Lean 4.33.1.

The principal theorem `border_count_le` says: for every finite binary partial
DFA with k states whose accepting states have no outgoing edges, every word
that reaches an accepting state from any initial control has at most k border
lengths, counting both 0 and the full length. It is proved by an injection from
border lengths to ORIGINAL run states. `suffix_positive_border_count_le`
specializes this to every suffix of the same run: at most k-1 nonempty borders.
Neither result bounds word length or the number of repeated source visits.

The finite-state/canonical-run premises are actual definitions and explicit
acceptance hypotheses. Injectivity and the bound themselves are conclusions,
not assumed fields. `cutState` is executable and its fallback is unused on a
defined full run; `runFrom_cutState_drop` proves the needed suffix contract.
The structural proofs require no flag or Bad-state hypotheses and therefore
apply in particular to accepted witnesses, whose conditions are stronger.

This is the border-count dependency of the rank proof. The correspondence to
the implementation's recursive failure-link depth, reversal of its prefixes,
and first-milestone/first-return correspondence remain to be formalized. The
module must not be described as a Lean verification of the entire rank driver.

## Executed verification

At proof commit `e905c7c7938cd26aa45b0101d321cdd7f1f1b80d`, the dedicated
[Lean rank foundation run](https://github.com/mhenglein/subtail/actions/runs/35307090239)
completed successfully. It compiled the new module, replayed its declarations
with the pinned bundled `leanchecker`, and audited all 13 named runtime/theorem
dependency closures. Only standard logical axioms are permitted for theorems;
runtime definitions additionally exclude Classical.choice. Research axioms,
sorryAx and native-evaluation axioms are not permitted by the check.

The same job ran `python3 scripts/check_lean.py` successfully and verified the
existing saved Lean results were unchanged. This verifies the new proof and
preserves the existing core; it is not a claim that every other repository
workflow completed. No local Lean installation was available in the chat
container: these Lean executions occurred on the repository's GitHub runner.
The locally saved source matches Git blob `8333123477230f5fd88edc0f7f6cda9ff1ee2619`.

The first attempt had one implicit-library-argument elaboration error, repaired
without changing any theorem statement or adding a mathematical assumption.
Theorem statements were read back against the ordinary proof as above. This
readback was by the same assistant, not an independent human semantic review.

From the repository root:

```sh
cd lean
lake build +Subtail.TerminalRank
lake env leanchecker Subtail.TerminalRank
```

The axiom-audit commands are retained in
[the Lean workflow](../.github/workflows/lean.yml) (formerly `lean-rank-foundation.yml`, folded in on 2026-09-19).
The module is not yet imported by `lean/Subtail.lean`; the explicit build target
above and the new workflow check it. Integration should link this evidence from
A018 and the Lean README without changing the proposed global theorem's status.

## Remaining route, in dependency order

1. Define failure parents and prove the exact border-chain/rank recurrence.
   Connect reversed prefixes to the accepted forward suffixes covered here.
   Prove the milestone first-return lemma, including overlapping copies.
2. Define finite coloured prefix graphs and their first-return surgery. Prove
   exact agreement with literal prefix semantics, including old endpoint
   recolouring, exceptional wrap edges and singleton extensions.
3. Define the finite observer/query syntax and constructive finite diagram
   enumeration. Prove the uniform preimage equivalence in both directions.
   The generated base word is unknown, and every observer of a physical
   interval must use ONE shared interval word. This is the highest-priority
   difficult formalization, not an axiom to assume.
4. Prove closure under repeated compilation, the quantitative clause bound,
   and the proposed computable witness bound. Implement finite decision on
   the existing `Witness` predicate and prove its correctness and termination.
5. Formalize arbitrary prefix-closed path sets, conservative normalization,
   regular canonical models, satisfiability, summary construction, C029 and
   C031. Compose the executable algorithms to decide arbitrary-tree entailment.

The final interface is an executable `SEPInput -> Bool` with a correctness
biconditional against entailment over ALL allowed valuations. A theorem that
merely assumes the global bound or a `Decidable` oracle does not meet it.
Arbitrary path sets belong on the specification side; the executable algorithm
must not use classical choice as a runtime decision oracle.

Compilation checks the supplied formal statement; a separate readback must
check that it is the intended mathematical statement. Lean's proof-validation
reference explains both the axiom audit and this semantic distinction:
https://lean-lang.org/doc/reference/latest/ValidatingProofs/

The full candidate remains a proposed ordinary proof. Formalization can expose
an actual gap; successful verification of this foundation does not guarantee
that the uniform closure theorem will formalize unchanged.
