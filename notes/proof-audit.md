# Proof audit: `sep-topfree.pdf`, Sections 1--6

Printed-page references below use the page number in the PDF footer.

## Overall status

The core top-free characterization is sound for the semantics stated in Definition 1.1: variables range over arbitrary, possibly infinite trees. Theorem 4.2 is a valid corrected low-water/cap decomposition, and the border reduction in Section 5 follows from it. The open part is still the prefix/border avoidance decision problem; Sections 1--6 do not provide a decision procedure.

The memo must keep three semantics separate:

* `finite trees` means finite `X(t)`;
* `regular trees` in Theorem 2.6/Corollary 2.7 means possibly infinite trees whose `X` language is regular;
* `arbitrary trees` includes both.

Corollary 2.7 proves arbitrary entailment equals regular (possibly infinite) entailment. It does not prove equality with finite-tree entailment. In fact, `C0 = {alpha x beta <= alpha}` is satisfiable in the memo's semantics but has no finite model: `epsilon in X_alpha` and `0 X_alpha subseteq X_alpha` force every `0^n` into `X_alpha`. Thus the same `C0` entails every target vacuously under finite-model semantics, while Theorem 3.2 gives a countermodel under arbitrary/regular semantics. Any finite-tree claim needs a separate argument and cannot use C0 as a satisfiable example.

## Established arguments

1. **Sections 1 and 2.** The identification of a type with a prefix-closed `X`-set, the inclusion clauses in Lemma 1.8, the propagation system `W`, and the least-solution/satisfiability argument in Proposition 2.5 are correct for arbitrary possibly infinite trees. For formal precision, the inverse map from a prefix-closed `X` should have domain `D={epsilon} union X union X{0,1}`, put product on X, and put bottom on `D minus X`. This includes a bottom root when X is empty. The current sentence on p.3 is shorthand and can be misread as omitting that root.

2. **Theorem 2.6 (p.5--6).** The three conditions are exactly what the canonical closure needs. `(S)` protects the alpha-prefix seeds from denial states, `(F)` protects them from unconditional product facts, and `(B)` separates alpha from beta. The converse argument from an arbitrary countermodel is sound. The regularity conclusion is also sound: pushdown saturation gives a regular reachable configuration set from the finite prefix seed set.

   There is one proof omission in the `(S) => countermodel` paragraph on p.5: `(S)` covers only the branch seeded by prefixes of `p`. The displayed `X_v` also contains the closure of the unconditional seeds `<gamma,epsilon>` for `gamma in BF`. To conclude that no denial state is reached on this branch, the proof must explicitly invoke satisfiability of `C` and Proposition 2.5. Without that invocation, “By (S) it meets no denial” does not follow from `(S)` alone.

3. **Theorem 2.10 (p.6--7).** The forward reduction to PrefixAvoid is correct. The stated converse is only a transition-skeleton observation. Encoding one push/pop with a product constraint adds a fresh dead-end branch, which is harmless for paths between original states, but the proof does not establish that an arbitrary regular restriction `R` can be realized as the specific `(S) intersection (F)` side condition. The memo itself calls this step unfinished. Therefore Sections 1--6 establish `sep <= PrefixAvoid`, not an equivalence or a hardness result for PrefixAvoid.

4. **Sections 3--5.** The C0 counterexample to the old regularity lemma is correct. For `A = W^rev`, the language is

   `M = { 0^j 1 u : j >= 0 and u is a prefix of (0^j 1)^omega }`,

   and its intersection with `0* 1 0* 1` is `{0^j 1 0^j 1 : j >= 0}`, so it is nonregular. Theorem 4.2's decomposition follows by choosing a minimum-height configuration, erasing the untouched bottom suffix, and applying `u prefix z u iff z = epsilon or u prefix z^omega`. The proof requires exactly the advertised push/pop/epsilon transition model. Lemmas 5.1--5.3 then correctly translate the cap condition into periods and borders, including the explicitly intended empty and full borders.

## Section 6 findings

1. **The Caucal citation itself is appropriate.** Caucal's Theorem 1.3 concerns a finite rewriting system and gives rational prefix rewriting; the sharper `K . Delta` form is the relevant right-synchronized form. The finite-rule hypothesis matters. The mirrored suffix example in Proposition 6.6 is a valid warning for an infinite/rational rule relation.

2. **Finiteness is attributed to the wrong source.** Proposition 6.2 says the finite flag alphabet follows because `K` in equation (1) is recognizable. In this application the index set is already the finite pushdown state set `Q`, and the summary languages are regular by standard pushdown reachability. Theorem 4.2 itself already proves the finite union over `gamma in Q`. Caucal supplies a useful general factorization, but it is not needed to establish finiteness of the flags here. The phrase on p.10 that Caucal is “genuinely load-bearing” for the finite class set should be weakened.

3. **Remark 6.3 overclaims a restriction.** The intersection form

   `G((A,B),(A',B')) iff A' intersection B is nonempty`

   is universal if the auxiliary state set may grow. For any finite relation `H` on classes `k_1,...,k_n`, take `Q={1,...,n}`, `B_{k_i}={i}`, and `A_{k_j}={i : H(k_i,k_j)}`. Then the intersection form realizes exactly `H`. Any genuine restriction must come from joint realizability by the two summary automata and from which class sequences one DFA can produce, not from the bare intersection formula. The experiment in Remark 6.3 should therefore be described as testing a fixed-summary/transition subclass, after defining that subclass precisely; it does not establish that intersection-shaped relations are a proper subclass of arbitrary abstract `G`.

4. **Theorem 6.5 needs a fixed-state slice.** The nonrationality proof is valid for the relation

   `{(w,w') : <beta,w> ->* <alpha,w'> and w' prefix w}`

   with the states fixed to the C0 pair. If `->*` denotes the full reflexive relation on configurations, its identity pairs already add every `(q w,q w)` and the displayed projection is not literally `L^{beta alpha}`. State the slice explicitly before applying the “domain of a rational relation is regular” argument.

5. **Scope of the negative conclusions.** Propositions 6.4--6.6 rule out particular closure arguments inside rational/recognizable transductions. They do not prove that no other consequence of Caucal's theorem, no finite-state encoding, or no augmented finite system can help. The claims that an augmented system is necessarily infinite and that the MSO route is closed are plausible heuristics but are not established by the propositions as written; label them as conjectural strategy assessments.

## Consequence for the attack

The reliable boundary after Section 6 is:

`C not-entails alpha <= beta`
`iff` a path passes the regular side conditions `(S),(F)` and avoids the prefix-reach relation;
Theorem 4.2 identifies the latter relation as a finite union of regular heads plus periodic caps;
Section 5 turns it into flagged-border avoidance.

The remaining theorem needed for decidability is a bound on the witness/border budget in the later occurrence-form development. Sections 1--6 neither prove nor refute that bound. Experiments should preserve the finite-state system and test realizability constraints, while avoiding the inference that an arbitrary abstract flag relation is less general merely because it has an intersection presentation.
