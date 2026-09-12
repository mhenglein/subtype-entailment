# End-to-end route: finite closed-walk schemes

Date: 2026-09-12. Base: `52d5270342b27aee3cad10e1b2d0ac7d9307a580`.

## Final target

Decide subtype entailment over bottom and binary covariant product for arbitrary, possibly infinite trees. Via the repository's existing reductions, it suffices to decide arbitrary terminal BorderAvoid witness existence. Those reductions retain their existing written/audited status.

## Established inputs used here

1. C067 checks one fixed source position by unique terminal prefix captures and positive existential word equations with regular constraints.
2. C071 checks all repeated boundaries of a first-return loop power, with the exceptional conjugacy case included.
3. DGH Theorem 4 decides the resulting free-monoid formula fragment in polynomial space.

No proof-assistant re-verification of these dependencies is claimed.

## New discharged implications

1. A source-arrival counter lift preserves every original witness comparison exactly.
2. Any loop with a supplied number d of source arrivals is first-return in its d-counter lift; so is every rotation at a source occurrence.
3. Commutation plus return to the lifted pivot means an integral whole-base power, even for imprimitive words and repeated original source labels.
4. Applying C071 in phase-local lifts gives an exact finite formula for each supplied finite closed-source-walk scheme, retaining common word assignments and tails.
5. The construction is polynomial in the instance and the explicitly supplied scheme; the external theorem yields a PSPACE upper bound for that restricted input format.

See `RESEARCH_NOTE.md` for proofs. These are written proofs with executable finite regressions, not independently reviewed or Lean-checked claims.

## Undischarged implication

Find a total computable H(k) such that every positive k-state terminal instance has some witness in a scheme whose number of phases plus total listed base-source occurrences is at most H(k), or replace that cover by a different complete terminating representation.

A finite scheme can already represent unbounded copy exponents and unbounded source-free data paths. But allowing arbitrarily many unknown return words, arbitrarily long changing source walks, or an unbounded number of phases is NOT automatically covered by this exact fixed-scheme result.

## Falsification conditions

An attempted replacement must preserve a witness of the same original instance, including comparisons newly created at joins. The saved one-flag interior-deletion example refutes preservation from acceptance alone. Earlier repository examples refute complete-profile quotienting and naive source-by-source deletion.

A family needing many phases for one chosen decomposition is not enough to refute an existential bound: it must exclude all smaller witnessing schemes of the stated format. Conversely, agreeing finite searches do not prove coverage.

## Opposing route

An undecidability reduction whose positive outputs admit an effectively bounded scheme family of this format would be contradicted by the restricted decision theorem. A genuine negative construction must force interaction escaping every such effective bound, or invalidate a precise dependency with a counterexample.

The nearby trailing-context pattern reduction does not supply that result because terminal suffix comparisons have no arbitrary trailing context. No terminal-anchor gadget is established here.

## Current outcome

An exact extension of the symbolic decision interface, not a proof of unrestricted decidability and not an undecidability result. The next global obligation is stated rather than assumed.
