# Canonical Presburger selectors after candidate-changing normalization

Date: 2026-09-08. Workstreams A012/A016/A017. Follows the regular-middle erasure continuation.

**Status:** written consequence of the existing A016 fixed-skeleton translation plus a new finite regular-middle lift lemma. It is not a new Lean theorem and does not decide unrestricted Problem 1.7.

## 1. The selector-synthesis subproblem inside a fixed skeleton is complete

Fix one A016 skeleton

    s0 u1^n1 s1 ... ud^nd sd,    n1,...,nd >= 0,

for one annotated partial DFA. Let `A(n)` be the Presburger formula saying that the exponent vector produces an admissible accepted candidate. A016 already gives Presburger formulas for total length `N(n)`, state `c_n(x)`, letters at symbolic positions, and the exact witness condition.

Define

    V(n,i,j) :=
      A(n)
      and 0 <= i < j < N(n)
      and G(c_n(i),c_n(j))
      and forall h (0 <= h < N(n)-j -> letter_n(i+h)=letter_n(j+h)).

Every atom is Presburger by A016, hence `V` is effectively Presburger-definable. On a boundary-safe slice, order cut pairs lexicographically and put

    LeastV(n,i,j) := V(n,i,j)
      and not exists i',j' (Earlier(i',j',i,j) and V(n,i',j')).

For every bad admissible vector this defines exactly one pair; for every witness none.

**Theorem 1 (canonical fixed-skeleton selector).** For every supplied fixed skeleton, the graph of a canonical violating-cut selector is effectively Presburger-definable. The skeleton is NO exactly when

    forall n ( A(n) -> exists i,j LeastV(n,i,j) ).

This is decidable in Presburger arithmetic. Quantifier elimination may turn the selector graph into finite Boolean combinations of inequalities and congruences. Hand-written cases such as `n<m / n=m / n>m` are therefore explanatory certificates, not a completeness requirement for fixed-skeleton selector synthesis.

The selector need not be one affine function globally; congruence branches and finite exceptions may be necessary. The theorem also does not produce a selector before a finite skeleton has been obtained.

## 2. Bounded insertion exposure is an exact finite lift condition

Now let a reduced candidate have a distinguished insertion boundary `a(n)` and write

    r_n = A_n B_n.

The original family inserts an arbitrary word `M` from a fixed regular language `L` at that boundary:

    w_(n,M) = A_n M B_n.

Assume every `M in L`, when read from the original DFA state at the boundary, returns to that same state. This is exactly checkable by the product routine in `regular_middle_interface.py`. Therefore every state on the continuation `B_n` is unchanged after shifting its position by `|M|`.

Consider a reduced forbidden comparison selected at cuts `i<j` with

    i < a <= j.

In the original word lift the target cut to

    j' = j + |M|,

and leave `i` unchanged. The target suffix `w[j':]` is literally the reduced target suffix `r[j:]`, so its length

    ell = N-j

is unchanged. The source prefix of length `ell` differs from the reduced source only if it reaches past the insertion point. Define the **insertion exposure**

    d = max(0, i + ell - a)
      = max(0, i + (N-j) - a).

Only the first `d` symbols after the insertion boundary matter. The reduced source sees `prefix_d(B_n)`; the original source sees `prefix_d(M B_n)`.

For a fixed depth `d`, define a reduced-tail prefix `P in Sigma^d` to be **L-compatible** when

    prefix_d(M P) = P    for every M in L.

This wording abbreviates the natural continuation convention: when `|M|<d`, append the first `d-|M|` symbols of `P`; when `|M|>=d`, only the first `d` symbols of `M` are read. Equivalently:

* every accepted `M` with `|M|>=d` has prefix `P` of length `d`; and
* every accepted `M` with `|M|<d` satisfies `M P[:d-|M|] = P`.

Both sets are finite-state computable. `good_reduced_prefixes` implements exactly this characterization by enumerating the finitely many short accepted middles and the finitely many length-`d` prefixes that extend to an accepted middle.

**Theorem 2 (bounded-exposure lift).** Suppose on a fixed reduced skeleton:

1. the canonical selected comparison always satisfies `i<a<=j`;
2. its insertion exposure `d` is bounded by a finite `C`;
3. every middle word returns the insertion boundary state to itself; and
4. for every selected parameter vector, `prefix_d(B_n)` is an L-compatible depth-`d` prefix.

Then the selected reduced forbidden comparison lifts to a forbidden comparison in `A_n M B_n` for every `M in L`.

**Proof.** The state at `i` is unchanged. Because every middle returns the boundary state, the state at `j'` equals the reduced state at `j`, so the ordered flag is preserved. The lifted target suffix equals the reduced target suffix exactly. Before `a`, the lifted source segment equals the reduced source. Its only potentially changed part is its final `d` symbols after `a`; condition 4 says these are also identical for every `M`. Hence the first `ell` letters at the lifted source equal the lifted target suffix, giving the forbidden agreement. QED.

Because `LeastV`, `N`, `a`, `i`, and `j` are Presburger-definable, the set of possible exposure depths is Presburger-definable. Its boundedness and exact maximum are decidable by the same one-dimensional semilinear reasoning used elsewhere in the repository. For a bounded maximum `C`, condition 4 is a finite disjunction over `d=0,...,C` and the finite set of L-compatible words of each length. The statement that the symbolic reduced tail begins with one of those words is again Presburger by A016's letter-at-position formulas.

Therefore all four hypotheses of Theorem 2 are effectively decidable for a supplied fixed skeleton, regular insertion language, and insertion anchor.

### Six-state barrier benchmark

After erasing `M in (0^+11)*`, the reduced family is

    0^n 1 0^m 10.

Its canonical/simple three-case selector always has target at or after the insertion boundary. In the `n<m` branch the source comparison crosses the boundary by exactly one symbol; the other branches have zero exposure. The exact finite interface computation gives

    Good_0 = {epsilon},
    Good_1 = {0},
    Good_2 = empty.

The reduced continuation begins with `0`, so the depth-one branch lifts. This recovers the all-length erasure proof as an instance of the general bounded-exposure rule.

## 3. Consequence for regular-middle erasure

Suppose a nonflat candidate family has a candidate-changing normalization whose image is a finite union of A016 fixed skeletons. Then arithmetic selector synthesis is no longer open:

1. construct `LeastV` on every reduced skeleton;
2. decide exact reduced witness existence;
3. for each NO skeleton, decide whether the selected comparison is covered by Theorem 2 or another finite lift rule.

This decomposition isolates the genuinely new obligation: obtain a finite existence-preserving erasure cover and lift the canonical comparisons through the erased regions.

## 4. A genuine decidable nonflat class

Consider families represented as a finite union of triples

    (fixed reduced skeleton S, regular return-middle L, insertion anchor a)

with reconstruction `A_n M B_n`. Assume all accepted originals are covered by these triples. If, for each triple, either:

* the reduced skeleton has a witness and a stated witness-reflecting reconstruction condition produces an original witness; or
* the reduced skeleton is NO and its canonical selector satisfies Theorem 2,

then the original family is decidable by finitely many Presburger and finite-automaton computations.

This is genuinely nonflat: `L` may be the full return language of a productive SCC and contain arbitrarily long/nested recurrent paths. The theorem does not bound the number or length of those paths; it uses only their regular insertion interface and bounded exposure of the selected comparison.

The current branch mechanically discovers SCC return languages, checks the return-state condition, computes compatible bounded prefixes, and separately synthesizes constant-from-end selectors. It does not yet generate a complete finite erasure cover for every input.

## 5. What remains

For an arbitrary instance, canonical selectors may interact with an erased region in harder ways:

* both source and target lie before the insertion and therefore see the middle at different relative offsets;
* the target itself begins before the erased region;
* the exposure depth is unbounded;
* two erased regions interact in one comparison; or
* both compared occurrences consume a shared recurrent word and literal identity must be retained rather than replaced by a finite prefix.

The natural next abstraction is to classify selected comparisons by these finite intersection types. Cases in which both occurrences consume the same middle variable should feed the A017 shared-word backend; bounded one-sided crossings are handled by Theorem 2. A complete termination/coverage theorem for arbitrary recurrent components remains open.
