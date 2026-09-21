# Function-only variance: guarded closure survives, linear reachability does not

> Current status, 21 September 2026: the ordinary result was independently
> accepted in the [submission review](2026-09-20-submission-review.md).
> Its exact integrated scope is [C091](../research/claims.md#c091).
> [Current integration and reproduction](2026-09-21-publication-candidate.md).
> The dated author record below is preserved, including its original pending
> review status and execution limits.

Date: 2026-09-20. Author/session: `function-only-transfer-20260920`.
Parent #72; child/interface #74; coordination #37; A010/A011/A018.
Input revision: `19b06d4fed9da635d9b911f0e908d04e4fc4b099`.
Status: **ordinary proofs and independently specified diagnostic algorithms; independent mathematical review requested, not presumed obtained; no Lean result**.

## 1. Result, route and exact scope

For arbitrary trees over bottom and ONE binary function constructor, contravariant in argument 0 and covariant in argument 1:

* The subtype relation has an exact finite, polarity-sensitive, **active-path** characterization (Theorem 1).
* Finite expression constraints have an exact positive, guarded ground-Horn presentation. A least closure under **function-node inclusion**, and an exact finite-address seeded countermodel characterization, survive (Theorems 2-3).
* That closure is not additive in its seeds. Consequently it cannot be computed by a fixed graph with per-fact seed encoding and existential reachability decoding, even with signed or auxiliary controls (Theorem 4). This refutes the direct signed-control/reversed-edge transfer of the existing canonical pushdown reachability construction.
* Subtype-least solutions themselves need not exist (Proposition 5). This is different from failure of the positive-node least closure, which DOES exist.

These results do not prove undecidability, do not rule out other reductions, and do not transfer the existing complete decision to functions. All refuting models below are finite, so those refutations also apply when valuations are restricted to finite or regular trees.

The end-to-end route was fixed before supporting implementation: exact coinductive comparison -> active separating address -> guarded canonical closure -> try signed single-fact reachability -> finite summaries -> existing terminal/infinite backend. The fourth implication is refuted here; therefore no summary or compiler adaptation was implemented. A surviving route would have to give a finite effective treatment of the guarded closure AND terminate the search over all separating words. Neither follows from semantic monotonicity.

The coordinator explicitly agreed this three-path scope in #74, comment 5750364796. Existing Lean, shared ledgers, paper and other extensions remain unchanged. A remote branch is based on the input revision. Container DNS prevented cloning; the local Git worktree is explicitly a standalone diagnostic repository with an empty local base, NOT a checkout of that revision. No full repository or Lean run is claimed.

## 2. Domain, expressions and coinductive order

Let A={0,1}. A value is a rooted labelled tree whose nodes have label bottom or F. Bottom has no children; F has exactly children 0 and 1. Trees may have infinite, nonregular branches. Equivalently, specify an arbitrary prefix-closed set P(t) of F-labelled addresses in A*. Its labelled domain is {epsilon} union {wi : w in P(t), i in A}; members of P(t) have label F and the remaining domain nodes have label bottom. The empty set represents bottom. Define

    P(F(s,t)) = {epsilon} union 0P(s) union 1P(t).

This reuses only the SHAPE representation from `TreeSemantics.lean`, not its `Below` relation.

On relations R between values put

    Phi(R) = {(bottom,t) : t a value}
             union {(F(a,b),F(c,d)) : (c,a) in R and (b,d) in R}.

Define s <= t as the greatest fixed point nu Phi. Phi is monotone in R, notwithstanding contravariance in the first TYPE argument. Thus

    bottom <= t;
    F(a,b) <= bottom is false;
    F(a,b) <= F(c,d) iff c <= a and b <= d.

The fixed-point equation justifies inversion in both directions. Infinite unfolding is not a finite-depth cutoff. The identity relation is a simulation, proving reflexivity. Relational composition of <= with itself is a simulation: at a function root its first-coordinate intermediate comparisons reverse together. This proves transitivity. Mutual comparison forces equal root labels and, recursively at every finite depth, equal child labels, proving antisymmetry. Hence writing e=f as the two inequalities is legitimate.

Finite expressions are e ::= x | bottom | F(e,e), over a finite variable set V. A valuation maps every variable to one value in this domain. Evaluation is the indicated finite structural substitution. A finite constraint list C is satisfied when all evaluated inequalities hold. Entailment means

    C |= s <= t iff every valuation satisfying C satisfies s <= t.

Inconsistent premises entail every query. No finite/regular restriction, decidable node-membership predicate, explicit top or additional constructor is present.

## 3. Active addresses and polarity

Let p(w) be the number of 0 letters in w modulo 2. Appending or prepending 0 toggles it; 1 preserves it; p(uv)=p(u)+p(v) modulo 2.

An address w is active for s,t when every strict prefix v of w belongs to BOTH P(s) and P(t). The root is active. These are exactly the addresses in both labelled domains. At an active w, compare the two root labels normally when p(w)=0 and in reverse when p(w)=1.

**Theorem 1 (finite bad-address characterization).** s is not below t iff an active finite word w has one of the following mismatches:

    p(w)=0: w in P(s), w not in P(t);
    p(w)=1: w in P(t), w not in P(s).

**Proof.** If s<=t, unfold the fixed-point equation along w. Both trees have function nodes at every strict prefix, so each descent is justified. Argument 0 reverses the ordered pair and argument 1 preserves it. A mismatch would end with a function below bottom, impossible.

Conversely let R consist of pairs with no such mismatch. If the left root is bottom the pair belongs to Phi(R). Otherwise the right root must also be F. No bad address of the reversed domain pair (t0,s0) exists: prefixing it by 0 would give a bad address of (s,t), with exactly the required sign reversal. The same argument with 1 applies to (s1,t1). Thus R is postfixed, R subseteq Phi(R), and coinduction gives R subseteq <=. This proof includes arbitrary nonregular infinite trees. A branch that never reaches a bad finite address does not become an extra failure condition. QED.

### The unguarded signed encoding already fails

Put B=F(bottom,bottom), A=F(B,bottom). Bottom<=A is true. However the proposed all-address parity test requires, at the odd address 0, that 0 in P(A) imply 0 in P(bottom), which is false. The address is not active because the left root is bottom. This is a distinct obstruction from the extension study's already-known unsigned-inclusion counterexample A<=B.

Merely changing inclusion direction at odd addresses, or complementing unqualified odd-address membership, does not repair bottom masking. The empty word also must be checked: a nonbottom value is never below bottom.

## 4. Exact guarded Horn presentation

For a finite expression e, write M_e(w) for membership of w in its evaluated function-node set. Syntactically this reduces effectively to ONE variable atom N_x(u), the constant true, or the constant false:

    M_x(w)=N_x(w); M_bottom(w)=false;
    M_F(a,b)(epsilon)=true;
    M_F(a,b)(0u)=M_a(u); M_F(a,b)(1u)=M_b(u).

There is no independent atom for another occurrence of the same variable. On the fact universe V x A*, first include prefix rules

    N_x(vi) -> N_x(v).

For each e<=f in C include the root rule M_e(epsilon)->M_f(epsilon). For every nonempty w=vi include

    p(w)=0: M_e(w) AND M_f(v) -> M_f(w);
    p(w)=1: M_f(w) AND M_e(v) -> M_e(w).                 (H)

Simplify constants in these rules. A true head needs no rule; a false antecedent disables a rule; true antecedents disappear. Replace a false head by a distinguished atom BAD. No rule has BAD in its body. This is an effectively enumerable family of ground Horn rules, not a claim of a finite automaton presentation.

**Theorem 2 (exactness and least closure).** For every prefix-closed valuation rho, rho satisfies C iff its facts satisfy all these rules without BAD. For any seed set S, the least Horn closure Cl_C(S) exists, is monotone in S, and is contained in every BAD-free model containing S. If BAD is absent, its variable facts form a genuine model of C. Conversely, existence of any model containing S implies BAD is absent from the closure.

**Proof of exactness.** The full active guard for w is the conjunction of both memberships at all strict prefixes. In (H), membership at w on the antecedent side supplies all its own prefixes. Membership at v on the other side supplies all that side's strict prefixes. Thus the short guard is equivalent to the full active guard in the presence of prefix closure. The consequent forbids exactly the mismatch of Theorem 1. Root rules handle epsilon. Simplifying constants preserves truth, so this also covers explicit bottom expressions, repeated variables and inconsistent constraints.

**Proof of closure.** Take all facts with finite derivations from S by the definite rules (including BAD as a possible conclusion). Equivalently take the least fixed point of the inflationary immediate-consequence operator. Finitary rule bodies make the union of the finite-stage closures closed: all premises of a rule appear together at some finite stage. Induction on a derivation puts every derived fact into every model containing S. Prefix rules make each variable's derived node set prefix-closed. If BAD is absent, all original rules hold and exactness constructs a model. If BAD is present, derivation soundness excludes every model containing S. These arguments do not require finite S; finite seeds are used in Theorem 3. QED.

This is a least closure in positive-node inclusion, NOT in semantic subtype order. It can be infinite. Effective enumerability of derivations does not decide non-derivability. A finite-height experiment must not silently replace this closure.

### Exact connection to the existing implementation

At the input revision `lean/Subtail/CanonicalModel.lean`, constructors `Derived.leq`, `popLeft`, `popRight`, `pushLeft`, `pushRight` each have ONE derived premise. The source semantics there is covariant node inclusion. Its `canonical_least`, stack reachability and summary bridge rely on that exact unary propagation.

For the new constraint x<=y, even its first domain step is

    N_y(0) AND N_x(epsilon) -> N_x(0).

The second premise is real activation information. Erasing it is unsound; refusing the inference misses models' required facts. This is the point at which simply adding polarity controls and reversing graph edges loses the existing invariant.

## 5. Exact seeded countermodel theorem

For a query s<=t and finite w, let q=s,r=t if p(w)=0, and q=t,r=s otherwise. Require as positive seeds M_s(v),M_t(v) for every strict prefix v of w, together with M_q(w). Syntactically reduce these requirements as above: true contributes nothing, a variable atom becomes a seed, and false contributes BAD. Add the single denial M_r(w)->BAD, simplified in the same way. Let K(C,s,t,w) be the resulting least Horn closure.

**Theorem 3 (canonical separation, both directions).**

    C does not entail s<=t
      iff there exists w in A* with BAD not in K(C,s,t,w).

**Coverage.** Take any countervaluation, including a nonregular one. Theorem 1 supplies a finite active bad word. Every positive seed is true in that same valuation, and the forbidden endpoint is false. The valuation therefore satisfies the augmented Horn theory. Soundness of finite derivations excludes BAD from its least closure.

**Reconstruction.** If BAD is absent, Theorem 2 turns the closure's facts into one valuation satisfying every premise. All active-prefix seeds and the function endpoint are present. The added denial ensures the opposite endpoint is absent. Theorem 1 falsifies the query in this SAME valuation at this SAME address. No separate choice for an atom, occurrence or polarity is allowed. For w=epsilon the prefix set is empty and the root rule still applies. If C is inconsistent every augmented closure contains BAD, preserving vacuous entailment. QED.

This is a complete ordinary semantic theorem, not a decision procedure. In particular, testing that BAD never appears and completing the existential word search have not been given terminating algorithms here. No regular-countermodel theorem is inferred from C081's covariant one.

## 6. Counterexample to the named linear transfer

Fix C={x<=y}, and the finite values B,A from Section 3. Let S1 and S2 be the COMPLETE positive facts of these valuations:

    rho1: x=bottom, y=A;    S1={(y,epsilon),(y,0)};
    rho2: x=B,      y=B;    S2={(x,epsilon),(y,epsilon)}.

Both valuations satisfy C, so their fact sets are already closed: Cl_C(Si)=Si. Their union describes x=B,y=A, which is not a model: B<=A would require B<=bottom in the domain comparison. The rule above therefore derives (x,0) from S1 union S2, although it is in neither individual closure. Indeed Cl_C(S1 union S2) is exactly the fact set x=A,y=A.

**Theorem 4 (no fixed additive-reachability realization).** There are no data consisting of a fixed directed graph depending on C, fixed initial vertices K, a seed encoding iota with iota(S union T)=iota(S) union iota(T), and an existential reachability decoding, that compute Cl_C(S) for every seed set S. Signed controls, auxiliary vertices and even an infinite graph do not alter this statement.

**Proof.** Reachability distributes over unions of starting vertices:

    Reach(K union iota(S union T))
      = Reach(K union iota(S)) union Reach(K union iota(T)).

Decoding a fact by whether some representing vertex is reachable also preserves unions. Thus any represented closure would be additive. The explicit S1,S2 refute additivity. QED.

The excluded contract is precisely a fixed single-fact-reachability implementation of the canonical closure, including the straightforward signed-control adaptation of C081's W. A nonlinear seed preprocessing, conjunctive/alternating mechanism, different abstraction, or arbitrary entailment-preserving reduction is OUTSIDE this theorem. Even a compiler correct only for a restricted family of query seeds would need separate analysis; this theorem quantifies over all seeds and does not silently substitute that stronger obligation for every possible entailment reduction.

**Further exact-model obstruction.** There is also no finite conjunction of covariant bottom/product inequalities with existential auxiliary variables whose projection onto designated variables x,y is exactly the function-shape models of x<=y. Covariant expression evaluation commutes with coordinatewise nonempty unions of node sets, so the model set of any such conjunction is union-closed. Existential projection retains union-closure by taking the union of the two complete auxiliary valuations. The source relation above is not union-closed. This rules out an identity-on-shapes exact-model translation, not arbitrary encodings or reductions requiring only countermodel existence.

## 7. Subtype leastness, sharing and cycles

**Proposition 5.** The satisfiable system y=F(x,bottom) has no pointwise subtype-least valuation, over arbitrary, regular or finite values.

**Proof.** It has models (x=bottom,y=B) and (x=B,y=A). Any subtype-least model lies below the first, so x<=bottom and hence x=bottom. The equation then forces y=B. But B is not below A, contradicting that it lies below the second model. The witness models are finite, and the reasoning applies in every larger domain. QED.

Repeated variables cannot be independently assigned positive and negative trees. For example x occurs in both polarities in F(x,x), but N_x(u) remains one shared fact. Across a syntactic occurrence at address v, the sign is p(vu), not a new local choice. Recursion must preserve this same sharing on every traversal.

On a dependency path, signs multiply, or equivalently parities add. An even contravariant cycle returns to the same sign; an odd one returns to its opposite and only a second traversal restores it. A one-sign-per-control labelling would require parity consistency around every cycle (and between every pair of alternative paths); odd cycles obstruct that labelling, NOT existence of a tree or greatest-fixed-point comparison. Doubling controls records parity but does not remove the Horn activation conjunction.

For instance X=F(X,bottom) has the regular zero-spine solution L with P(L)={0^n:n>=0}. It has an odd negative self-cycle, but is entirely consistent. Its two-state presentation is one function node whose 0 edge returns to itself and whose 1 edge reaches bottom. The mutual equations X=F(Y,bottom), Y=F(X,bottom) traverse an even two-edge negative cycle and also have this solution. Both equations force infinitely many nodes, so have no finite solution. In contrast, the inequality F(X,bottom)<=X DOES have the finite solution X=B, because F(B,bottom)=A<=B. Importing the covariant lower-self zero-spine rule would incorrectly rule it out.

No explicit top is being introduced. In the arbitrary domain there happens to be a greatest value G=F(bottom,G). To prove this by ordinary coinduction, use

    R = {(bottom,t) : all values t} union {(t,G) : all values t}.

Every bottom-left pair is in Phi(R). For a pair (F(a,b),G), the domain obligation (bottom,a) and the codomain obligation (b,G) both belong to R. Thus R is postfixed and every t<=G. G is an infinite right spine, not an extra top-labelled leaf. This observation supplies neither an encoding of an explicit-top theory nor a finite-model result.

**Author readback correction.** The first version of this auxiliary paragraph used only the pairs (t,G) and mistakenly called that relation postfixed. The missing pairs (bottom,t) are now explicitly included. The conclusion, Theorems 1-4, Proposition 5 and the diagnostic code are unchanged. This is an author correction, not independent review.

## 8. Finite and regular boundaries

Theorems 1-2 describe all arbitrary values. Their order tests restrict correctly to finite and regular inputs. The explicit obstructions of Sections 3, 6 and 7 use finite models and thus refute the named transfers in every variant.

Theorem 3 has a finite-model refinement: a finite countermodel exists iff some augmented safe least closure has finitely many variable facts. In the forward direction that closure is contained in the finite countermodel; in the reverse direction reconstruct its finite trees. This is an exact additional condition, not an effective finiteness test.

For regular valuations, a subset of a regular language need not be regular. Therefore the least-closure argument alone does NOT establish regular countermodels or equivalence of regular and arbitrary entailment. The covariant R1-R4 construction cannot be imported without a guarded-closure regularity theorem.

The equations X=F(X,bottom), queried by X<=bottom, distinguish finite and arbitrary entailment: finite entailment is vacuously true; the regular infinite zero spine refutes the query in both the regular and arbitrary domains.

For TWO SUPPLIED finite graphs, comparison itself is decidable by eliminating failing pairs from the finite candidate simulation relation, or by reaching a bad signed pair. Termination is bounded by the finite pair-state set. This solves ground regular-type comparison only, not synthesis or universal entailment over unknown valuations. The diagnostic checker uses both independently specified methods.

## 9. Primary literature comparison

The following sources were read directly where described. These are bounded comparisons, not a claim that no other result exists. No external decision theorem is imported into Theorems 1-5.

**Henglein-Rehof, ICALP 1998, Sections 2 and 4, Theorem 1.** The author-uploaded original text defines address parity by the number of domain selectors and compares labels on the COMMON labelled domain. Section 4's nonstructural PSPACE-hardness construction uses product-only expressions in an ambient theory with bottom/top; it explicitly forces the query variable to the full infinite product tree. This is not a pure bottom/function hardness theorem. The parity/common-domain idea is prior art; our Theorem 1 specializes and reproves it rather than claiming it as new. Original manuscript text: https://www.researchgate.net/publication/2310458_Constraint_automata_and_the_complexity_of_recursive_subtype_entailment (author upload by Jakob Rehof). DOI: 10.1007/BFb0055089. The displayed hosting date is not the 1998 conference date.

**Niehren-Priesnitz 1999, Section 2 and Theorem 14.** The proved PSPACE-complete restricted syntax consists of product equations and variable inequalities; the ambient domain still contains bottom AND top and the product is covariant. Syntactically excluding constants does not exclude their values. Therefore this theorem is not a direct upper bound for the present bottom-literal, function-only input. Author manuscript, PDF indices 3 and 9: https://www.ps.uni-saarland.de/Publications/documents/SubTypeEntailment_99.pdf .

**Niehren-Priesnitz 2003, Section 2 and Theorem 1.** The stated signature is {bottom,f,top}, with f covariant. Section 2 explicitly excludes contravariant constructors and says extending the framework is possible but not fully obvious; it does not supply the required transfer there. Theorem 1 characterizes the problem by restricted cap-expression universality for finite, regular and arbitrary trees. It is not a decision theorem for that universality problem. Neither the top-free restriction nor the new guarded closure is thereby discharged. Author manuscript, PDF indices 2 and 6: https://www.ps.uni-saarland.de/Publications/documents/SubTypeEntailment_02.pdf .

**Schubert 2021.** The arXiv version 2 record, revised 20 December 2021, marks the claimed finite/regular PSPACE result withdrawn because the formulation of Lemma 5.5 invalidates the later construction. It is not an available upper-bound theorem: https://arxiv.org/abs/2109.02458 .

Source-access limits: the NP PDFs were available as parsed primary text; requested web screenshots failed, and a container PDF download also failed. No visual PDF inspection is claimed. The HR98 author-upload text was inspected as HTML; its PDF link was unavailable. These access limits do not enter the self-contained proofs above. No full archival literature-absence claim is made.

## 10. Validation, review interface and remaining obligations

Minimal nested-tuple finite-tree falsification was executed BEFORE supporting machinery, independently of the repository semantics or proposed Horn code. It confirmed the inactive odd-path counterexample, the union counterexample, the two-model leastness obstruction, and the finite solution of F(X,bottom)<=X.

The standalone standard-library checker is `experiments/check_function_only_transfer.py`; its receipt is `results/function-only-transfer.json`. It compares literal finite recursion, address-guard truth, finite-graph greatest-fixed-point elimination and signed bad-pair reachability. The receipt records actual counts and limits; tests are not universal proofs or a Lean run. No original covariant module is imported or edited.

Independent mathematical review is requested on this pinned note, particularly: (a) the common-domain/short-guard equivalence; (b) the single-atom expression expansion and BAD-free reconstruction; (c) both directions and all quantifiers of Theorem 3; (d) whether the explicitly additive seed contract in Theorem 4 is accurately distinguished from weaker existential entailment compilers; and (e) finite versus regular restrictions. Algorithmic differential checks by this author are NOT independent mathematical review. Formalization and Established status await that review.

A useful next interface is an effective analysis of the guarded Horn schema (H), preserving shared facts and query seeds, rather than modifications to the completed covariant theorem. This report makes no commitment to decidability or undecidability of that schema. The broader #72 remains open; no shared claim ID or status is changed by this note.
