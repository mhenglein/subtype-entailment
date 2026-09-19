# Complete expression-level entailment decision: route and proof record

Date / author: 2026-09-19, Codex Astra entailment-completion-20260919.
Approaches: A010/A013/A018; C029/C031 and the qualitative stage-6 part of C080.
Base: e21c599388e32e3d024f3efcde9e3500e838bdcd. Normalization integration: #49/#50/#52.
Status: proposed composition of independently checked components; final theorem and combined validation pending.

## Exact input and intended conclusion

For every natural n, a finite list G of pairs of finite expressions over Fin n,
bottom and one covariant binary product, and two such expressions s,t, construct
a total executable Boolean entailsCheck G s t. Its required theorem is

`entailsCheck G s t = true iff ExpressionNormalization.ExprEntails G s t`.

ExprEntails quantifies over every valuation into the existing TreeSemantics.Tree:
arbitrary prefix-closed product-node sets, including infinite and nonregular
ones. The premises are the original G. The queried inequality is not an added
premise. No satisfiability, finite-model, regular-model, witness-bound or
quantitative U/F assumption belongs in the final theorem.

## Objects and construction contracts

The checked normalizer collects product occurrences and used bottom from both
the premises and query. Its Naming has n+P+B variables and finite definitions;
old variables keep their indices. Both defining inequalities fix each product
slot, including duplicates; the bottom slot is constrained by a denial. Its
ordinary and Lean model extension/restriction proofs preserve query meanings
and each separating address. The separate Python reference has a different
allocation order; its evidence is not transferred to the Lean implementation.

For a normalized finite C and variables a,b, the existing SummaryAutomaton
constructs I with the finite carrier of pairs of control subsets, Boolean
alphabet, exact last-letter Pop transitions, canonical initial pair, final
forced-root exclusion, prefix-denial/UNSAT Bad bits and directed intersection
flags. Its witness_iff_separation preserves the same finite address. Strong
absorption holds for all states, not only reachable ones.

The existing C031 terminalize removes unsafe transitions before identifying
safe original final sinks. The C029 total Boolean decides InfWitness I under
the proved absorption condition. The terminal total Boolean decides original
Witness on terminalize I, whose terminality is proved. Neither operation uses
a search cutoff. Their raw combination is the negation of their Boolean OR.

## Route from start to finish

1. normalize_entails_iff: original ExprEntails iff normalized Entails. Already
   checked/reviewed in #49/#52; integrate unchanged source and fresh checks.
2. not_entails_iff_infinite_or_terminal: normalized non-entailment iff
   InfWitness I or terminalWitnessCheck (terminalize I)=true. Checked on main.
3. infiniteWitnessCheck_correct plus summary_absorbing replaces InfWitness by
   the executable C029 Boolean. Checked on main; apply at exactly the same I.
4. Negating the disjunction yields normalized Entails iff the negated Boolean
   OR is true. This Boolean-composition theorem is the new obligation.
5. Apply (1) to get the unconditional expression-level Boolean theorem. This
   is the second new obligation. Any added runtime short circuit must get its
   own semantic proof and leave this theorem unconditional.

All input constructions and both branch algorithms are total Lean definitions
on finite data. Classical reasoning may occur in erased propositions, but no
executable definition may depend on Classical.choice. The full imported
runtime dependency closure is audited separately from the correctness proofs.

## Necessary target and practical limits

The target is decidability, not a prescribed witness bound, complexity estimate
or practical performance. The existing exhaustive compiler can be enormous.
Resource-limited test execution returns UNKNOWN, never a negative decision.
No new normalization, C030 converse or U/F argument is needed for this route.

## Discriminating falsification

Check exact signatures and original semantics: no reversed inequality, extra
SAT premise, finite-tree replacement, omitted query-only variable, query added
as premise, or dropped incoming flag column. Preserve zero original variables,
bottom, duplicate product slots, UNSAT and necessarily infinite models. Native
tests should use independently justified answers or explicit countermodels;
a bounded model census cannot establish a universal positive answer. Compare
the raw Boolean branches and full frontend only where execution is feasible,
and state which paths were actually exercised. Retain both independent
normalization suites and their different allocation conventions.

## Opposing route and review

A successful final equivalence rules out undecidability for precisely this
finite-syntax, bottom/product, arbitrary-tree semantics; it says nothing about
other constructors or finite-tree interpretations. A failure in composition
must identify the mismatched hypothesis or semantic definition, not be patched
by assuming a bound or restricting valuations. One independent reviewer will
read the final declaration and semantic chain, separately from the author and
from the prior normalization readback. Whole-library kernel replay, axiom/
runtime audits and combined CI are required before final canonical promotion.

## Execution record

Pending: composition implementation, independent final readback, combined
validation and serialized main publication. The exact checks, limits, source
revisions and remaining obligations will replace this pending handoff.
