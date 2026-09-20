# Finite-tree entailment by excluding unbounded growth

Date/author: 2026-09-20, finite-trees-20260920. A010/A018; #58/#37.
Base: bb9295429ccdeb0cdbad5655e30582eaf77f6361.
Status: complete candidate route, under focused falsification and review.

## Exact input and conclusion

Let C be any finite list of normalized constraints over n variables, bottom
and one covariant binary product. A finite tree has finitely many product
addresses, equivalently a finite bound on their lengths. Let W=systemOf(C).
For controls q,m put L(q,m)={c : Pop_(reverse W)(q,c,m)}. Define
H={m : L(q,m) is infinite for at least one q}. Let C_fin append a denial
x_m<=bottom for every m in H. The target is the unconditional equivalence

    C entails a<=b over finite trees
      iff C_fin entails a<=b over arbitrary trees.

A second target is exact finite-model satisfiability by the same transformation.
Finite-expression inputs must normalize with finite values preserved both ways.
No satisfiability, regularity or witness bound is assumed. This does not assert
that all arbitrary models of C_fin are finite.

## Finite construction

The reverse-pop epsilon NFA has exactly the n control states. Its epsilon
edges are the least balanced relation of reverse W; a letter-a edge p->q is
a reverse-W pop-a rule. Initial q and final m give L(q,m). It is effective by
finite balanced saturation. A language is infinite precisely when an initial-
accessible, final-coaccessible cycle consumes a letter. Epsilon-only cycles
cannot make its word lengths unbounded.

Because H existentially quantifies the initial control q, compute the finite
unlabelled reachability relation T of balanced epsilon and pop edges. For
each letter edge p-a->r with T(r,p), mark every m with T(r,m). Their union is
H. A marked edge closes a nonempty-word cycle. Conversely an arbitrarily long
accepted word forces two equal controls around at least one consumed letter.
This equivalence must be independently tested and reviewed before use.

## End-to-end argument and obligations

1. **Necessary denials.** If a model has a product node (m,z) and m is Hot,
   reverse-pop words c of arbitrarily large length propagate that node to
   (q,c z). This contradicts finiteness at q. Thus every finite model of C
   satisfies the added denials. Need exact propagation orientation.
2. **Finite-closure criterion.** For every finite seed set S, its whole W
   reachability closure is finite iff no reached control belongs to H. The
   forward direction is step 1. For the reverse direction minimum-stack
   factorization writes each reached word as c z, where z is a suffix of a
   seed word and c belongs to L(q,m) for a reached intermediate control m.
   Finitely many seeds, suffixes, controls and finite languages give a finite
   union. This is the critical semantic proof target.
3. **Sufficiency for entailment.** If C_fin has an arbitrary countermodel,
   its finite separating address seeds a safe canonical closure. Added denials
   exclude H, so step 2 makes that canonical countermodel finite. Adding
   denials changes neither propagation nor forced roots. Therefore a finite
   countermodel to C exists. This closes the other direction; no assumption
   that the original arbitrary countermodel is finite is needed.
4. **Satisfiability.** The forced-root seed set alone yields the same argument.
   If C_fin is satisfiable, its safe least closure is finite. If C is finitely
   satisfiable, step 1 gives a C_fin model.
5. **Finite syntax.** Definitional product/bottom names have finite values
   under finite valuations, by structural induction. Restriction preserves
   finiteness. Exact normalization thus transfers the theorem to finite
   expression constraints/queries. Hot must be computed from the normalized
   system, including its names, before adding denials.
6. **Decision.** Compute C_fin effectively and call C081. Negative answers
   have finite canonical countermodels. A bounded execution remains UNKNOWN.
   The C081 call is checked; Python reduction must retain its own trust label
   unless every transformation theorem is actually formalized.

## Falsification and review

Check zero-spine vacuity, epsilon cycles, balanced push/pop loops with bounded
language, non-forced but Hot variables, Hot propagation to other controls,
multiple bottom names and zero variables. Compare H with an independent exact
NFA test based on existence of an accepted word of length at least n. Compare
reduction answers with exhaustive finite valuations only when an independent
input-specific depth bound proves that enumeration complete. Check returned
graphs for cycles reachable from original roots, not unreachable scratch nodes.

A separate read-only reviewer is testing the whole argument independently.
The Lean worker will name an exact finite-tree semantic/closure contract before
writing the new module. Any supplied Hot classification or finite bound remains
an explicit hypothesis until its bridge is proved. One conditional formal
lemma does not establish the computability part. Existing C081 and C084 sources
are read-only. This targets one signature/domain transfer and does not imply
anything about explicit top or contravariant constructors.
