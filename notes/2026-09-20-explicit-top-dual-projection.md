# Explicit top: dual-projection route

Date: 2026-09-20. Actor: explicit-top-dual-projection-20260920.
Workstreams: A010/A011/A018; issue #71; coordination #37.
Source base: 19b06d4fed9da635d9b911f0e908d04e4fc4b099.
Status: exploratory outline, NOT an established theorem. This initial version precedes supporting implementation and will be expanded in place.

## Exact input and intended conclusion

Finite expressions and finite conjunctions of inequalities over variables, bottom, top and one binary covariant product. Values are ALL arity-consistent labelled trees, including infinite nonregular trees. Bottom and top are nullary and respectively least/greatest. Products compare componentwise. No top/product identification is permitted. Entailment is universal implication, including vacuous truth for inconsistent premises.

Target: a total decision procedure for this entire signature by an effective reduction to the completed top-free C081 decision. No claim about complexity, finite-tree semantics, other labels or variance.

## Objects and construction contracts

Let W={0,1}*. Totalize a labelled tree's labels below a bottom leaf by bottom, and below a top leaf by top. Let P be its non-bottom language and H its top language. Proposed exact representation: P is prefix-closed, H is a right ideal, H is contained in P. Comparison should be precisely coordinatewise inclusion of P and H. Equivalently, Q=W\H is prefix-closed and P union Q=W; compare P covariantly and Q contravariantly.

Name all finite subexpressions, including query subexpressions, using fresh variables and exact equations. The common normalized system has x<=y, x=bottom, x=top, x=y*z. Shared source variables retain a single name.

Define C+ over top-free arbitrary trees by preserving inequalities/product equations, retaining bottom, and replacing top by a fresh omega satisfying omega=omega*omega. Define C- by reversing inequalities, swapping bottom/top, preserving products, then applying the same replacement. The omega equation uniquely forces the full infinite product tree, used ONLY in these projections, not as a claimed embedding of labelled top.

## Route from start to finish

1. Prove the labelled-tree/two-language bijection and the exact order characterization, for arbitrary sets, by finite-address arguments (OPEN at this outline).
2. Prove exact naming extension/restriction for all models and failed queries (standard but to be written).
3. Construct H as the least language family generated from ALL words at named top constants by the common inequality and product push/pop rules. Prove every derivation is stable under appending a common right suffix, so H is a right ideal (OPEN).
4. Prove H is contained in EVERY C+ model P. From ANY C- model Q, prove H is disjoint from Q. Hence H has no empty word at a product-equation root and is empty at bottom constants. Reconstruct a labelled model with exactly the supplied P component. This is the crucial universal-projection lifting obligation (OPEN).
5. Dualize step 4. Obtain surjectivity of both projections when both projected systems are satisfiable. In particular, source satisfiability iff Sat(C+) and Sat(C-).
6. Derive the precise entailment decomposition:

   Ent_source(C,a,b) iff not Sat(C+) or not Sat(C-) or
   (Ent_topfree(C+,a,b) and Ent_topfree(C-,b,a)).

   A failed conjunction needs only ONE projected countermodel; its lift must satisfy the WHOLE shared system and preserve that separating address. Independent witnesses for individual premises are not used.
7. Apply C081 to the two query checks and to satisfiability (unsatisfiability is entailment of the fixed false inequality bottom*bottom<=bottom). Four finite calls terminate. This uses C081's exact arbitrary-tree theorem, not a bounded implementation or a new assumed witness bound.

## Necessary target versus convenient strengthening

The target needs existence of a labelled countermodel for each failing projection. Step 4 proposes the stronger statement that every projected model lifts, once the other projection is satisfiable. A counterexample to this lifting would refute this route, not undecidability or every encoding. Arbitrary independent P and Q cannot simply be paired: both may omit the same word. The least H is the proposed repair.

## Falsification and opposing route

Use a literal labelled finite-graph subtype checker (including cyclic graphs), independent of language propagation. Test top vs top*top; a product lower bound with top target; inconsistent top<=bottom; shared variables; product equations with repeated children; zero spines; x=x*x and x<=y; and conflicting recurrent constraints. All finite/capped model searches remain UNKNOWN unless they produce an exact witness. Compare projection order, reconstructed models and original failed queries, not only projected satisfaction.

Keep undecidability live until the lifting theorem is proved: a failed right-suffix invariant or compatibility obstruction would identify a concrete place for a computation encoding. General first-order undecidability, or failure of top-to-omega alone, is not a negative theorem for this Horn entailment problem.

## Review and selective formalization

Primary literature must be read at exact statements; NP99 Theorem 14 excludes constants syntactically, and general first-order undecidability is not imported as entailment undecidability. Check later results' value domains separately.

No independent mathematical reviewer has yet reviewed this route. A reviewer is requested through #71/#37, not claimed launched. Planned selective Lean target: the all-word suffix stability and the common-model lifting/decomposition, in a NEW module only. The current runtime has no lean/lake and no full repository checkout; any unexecuted build is NOT RUN. The local workspace is an isolated partial-source git worktree, not a full clone or a claimed replay of C081.

Next decisive question: does the least right-ideal top-language construction lift EVERY positive projection under satisfiability of the negative projection, including recurrent shared-variable systems?
