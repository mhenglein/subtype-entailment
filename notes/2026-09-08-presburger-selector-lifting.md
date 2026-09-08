# Canonical Presburger selectors after candidate-changing normalization

Date: 2026-09-08. Workstreams A012/A016/A017. Follows the regular-middle erasure continuation.

**Status:** written consequence of the existing A016 fixed-skeleton translation. It is not a new Lean theorem and does not decide unrestricted Problem 1.7.

## 1. The selector-synthesis subproblem inside a fixed skeleton is complete

Fix one A016 skeleton

    s0 u1^n1 s1 ... ud^nd sd,    n1,...,nd >= 0,

for one annotated partial DFA. Let `A(n)` be the Presburger formula saying that the exponent vector produces an admissible accepted candidate. A016 already gives Presburger formulas for:

* the total length `N(n)`;
* the state `c_n(x)` at every guarded symbolic position;
* the letter at every guarded symbolic position; and
* the exact witness condition.

Define the proper forbidden-comparison relation

    V(n,i,j) :=
      A(n)
      and 0 <= i < j < N(n)
      and G(c_n(i),c_n(j))
      and forall h (0 <= h < N(n)-j -> letter_n(i+h)=letter_n(j+h)).

Every atom in this formula is Presburger by the A016 construction. Hence `V` is effectively Presburger-definable. Boundary failures may either be included as separate selector kinds or removed first by the repository's boundary normalization; below assume the boundary-safe slice.

Now order cut pairs lexicographically by `(j,i)` (shorter target position first, then source position), or by any other fixed Presburger-definable total order on the finite rectangle `0<=i<j<N`. Put

    LeastV(n,i,j) := V(n,i,j)
      and not exists i',j' (Earlier(i',j',i,j) and V(n,i',j')).

This is again Presburger. For every bad admissible exponent vector it defines exactly one pair; for every witness it defines none.

**Theorem 1 (canonical fixed-skeleton selector).** For every supplied fixed skeleton, the graph of a canonical violating-cut selector is effectively Presburger-definable. The skeleton is NO exactly when

    forall n ( A(n) -> exists i,j LeastV(n,i,j) ).

This statement is decidable by Presburger arithmetic. If desired, quantifier elimination turns the selector graph into a finite Boolean combination of linear inequalities and congruences. Thus hand-written cases such as `n<m / n=m / n>m` are explanatory certificates, not a completeness requirement for fixed-skeleton selector synthesis.

The result does NOT say that the selector is one affine function on all parameters. Congruence branches and finite exceptional regions may be necessary. It also does not provide a selector before a finite skeleton has been obtained.

## 2. Consequence for regular-middle erasure

Suppose a nonflat candidate family has a sound candidate-changing normalization

    E : original candidate -> reduced candidate

such that the image is a finite union of A016 fixed skeletons. Then the arithmetic part of a complete NO proof is no longer open:

1. construct the canonical `LeastV` relation on every reduced skeleton;
2. decide whether the reduced skeleton has any witness;
3. for a NO skeleton, use `LeastV` as the symbolic comparison to be lifted back through the erased regions.

For the six-state barrier benchmark, erasing `M in (0^+11)*` gives

    0^n 1 0^m 10,

which is a two-counter fixed skeleton. Its familiar three cases are one simple presentation of the canonical selector relation. The regular-middle erasure proof then shows that the selected comparison lifts for every allowed `M`.

This decomposition is useful because it isolates the genuinely new obligation:

> Given a canonical Presburger comparison selector on the reduced skeleton, decide/prove that at least one selected comparison lifts through every erased recurrent region.

The arithmetic selector is not the bottleneck.

## 3. A complete nonflat class obtained from any effective lift verifier

Let a **certified erasure cover** consist of finitely many original candidate families `C_t`, erasure maps `E_t`, and reduced fixed skeletons `S_t`, such that:

* the `C_t` cover every safe accepted original candidate;
* every `E_t(w)` lies in `S_t` and every member of `S_t` required for a positive direction has a stated reconstruction condition;
* for every `w in C_t`, if the canonical selector `LeastV` marks a comparison in `E_t(w)`, a finite interface certificate proves a forbidden comparison in `w`.

Then every covered NO reduced skeleton yields NO for its original family. If the cover additionally has witness-reflecting reconstruction for positive reduced members, running the exact A016 solver on the finite reduced cover decides the original instance.

This is a genuine nonflat decision scheme because the erased regions themselves may contain productive SCCs with arbitrarily many traversals. It is only a scheme until the cover and lifting certificates can be generated effectively for a stated class.

## 4. What remains

The next algorithmic target is therefore not generic arithmetic case discovery. It is an effective **lift verifier / erasure-cover generator**. The current branch already computes two finite interface ingredients exactly for a proposed regular middle:

* whether all middle words preserve a required original boundary state; and
* their maximal common nonempty prefix.

It also automatically extracts SCC return languages. These suffice for the six-state benchmark because its canonical selectors inspect no middle interior beyond one forced leading zero. General selectors may cross an erased region more deeply or compare two occurrences whose relative interaction depends on the entire shared middle word.

A promising next finite abstraction is to classify each selected comparison by how its two compared intervals intersect each erased region: neither side, source only, target only, both aligned, or one interval entering/leaving the region. Cases in which both sides consume the same regular middle variable can preserve literal identity rather than quotienting it to a transition action. The shared-word machinery from A017 is the natural backend for those cases.

No termination/completeness theorem for arbitrary recurrent components is claimed here.
