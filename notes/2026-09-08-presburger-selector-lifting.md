# Canonical Presburger selectors after candidate-changing normalization

Date: 2026-09-08. Workstreams A012/A016/A017. Follows the regular-middle erasure continuation.

**Status:** written consequence of the existing A016 fixed-skeleton translation plus finite regular-middle lift lemmas. It is not a new Lean theorem and does not decide unrestricted Problem 1.7.

## 1. Selector synthesis inside a fixed skeleton is complete

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

Let a reduced candidate have a distinguished insertion boundary `a(n)` and write

    r_n = A_n B_n.

The original family inserts an arbitrary word `M` from a fixed regular language `L` at that boundary:

    w_(n,M) = A_n M B_n.

Assume every `M in L`, when read from the original DFA state at the boundary, returns to that same state. This is exactly checkable by the product routine in `regular_middle_interface.py`. Therefore every state on the continuation `B_n` is unchanged after shifting its position by `|M|`.

Consider a reduced forbidden comparison at cuts `i<j` with

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

Equivalently:

* every accepted `M` with `|M|>=d` has prefix `P` of length `d`; and
* every accepted `M` with `|M|<d` satisfies `M P[:d-|M|] = P`.

Both sets are finite-state computable. `good_reduced_prefixes` implements exactly this characterization by enumerating the finitely many short accepted middles and the finitely many length-`d` prefixes that extend to an accepted middle.

**Theorem 2 (bounded-exposure lift).** Suppose a selected reduced comparison always satisfies `i<a<=j`, its insertion exposure is bounded by `C`, every middle word returns the boundary state, and for each selected parameter vector `prefix_d(B_n)` is an L-compatible depth-`d` prefix. Then that selected comparison lifts to a forbidden comparison in `A_n M B_n` for every `M in L`.

**Proof.** The state at `i` is unchanged. Because every middle returns the boundary state, the state at `j'` equals the reduced state at `j`, so the ordered flag is preserved. The lifted target suffix equals the reduced target suffix exactly. Before `a`, the lifted source segment equals the reduced source. Its only potentially changed part is its final `d` symbols after `a`; prefix compatibility makes those identical for every `M`. Hence the lifted source still begins with the target suffix. QED.

Because `V`, `N`, `a`, `i`, and `j` are Presburger-definable, the set of possible exposure depths is Presburger-definable. Its boundedness and exact maximum are decidable. For a bounded maximum, the compatibility condition is a finite disjunction over finitely many depths and finitely many compatible words.

## 3. Exposure-optimal selector synthesis

A fixed lexicographic selector may choose an unnecessarily difficult violation even when another violation of the SAME reduced word lifts easily. The right object is therefore the best available violation relative to the insertion interface.

Call a violation **right-target** when either

    a <= i < j,

or

    i < a <= j.

The first kind is completely after the insertion and lifts for free: both cuts shift by `|M|` and the compared suffixes are unchanged. Give it cost zero. For the second kind give it cost equal to the exposure `d` above. Violations with `j<a` are left unresolved by this one-insertion rule and receive infinite cost.

For finite cost `c`, the relation

    CostV(n,i,j,c)

is Presburger-definable: it is `V(n,i,j)` conjoined with the appropriate finite-cost position case and the linear/max definition of `c`. Define

    BestCost(n,c) := exists i,j CostV(n,i,j,c)
      and not exists c' (0 <= c' < c and exists i',j' CostV(n,i',j',c')).

Thus the graph of the minimum finite interaction cost is Presburger-definable.

**Theorem 3 (exposure-optimal selector).** For a supplied fixed skeleton and one regular return insertion, it is decidable whether EVERY bad admissible reduced word has at least one right-target violation. On that domain it is decidable whether the minimum finite exposure costs are bounded, and if so their exact maximum `C` is computable. Moreover a Presburger selector can choose, for each bad parameter vector, a violation of minimum cost and then a fixed tie-breaking order among equal-cost pairs.

To turn this into a sound erasure certificate one additionally asks, for each `c<=C`, whether every minimum-cost selected pair of cost `c` sees at the reduced continuation an L-compatible prefix from `Good_c`. This is again Presburger because `Good_c` is finite and A016 makes the first `c` continuation letters definable.

Therefore a NO fixed skeleton can be certified through a regular return insertion whenever:

1. every bad reduced member has a right-target violation;
2. the best available finite exposure is uniformly bounded; and
3. every exposure-optimal selected continuation satisfies the exact finite prefix-compatibility test.

This is strictly stronger than fixing `LeastV` first. It automatically chooses the violation that interacts least with the recurrent insertion.

### Six-state barrier benchmark

After erasing `M in (0^+11)*`, the reduced family is

    0^n 1 0^m 10.

Every reduced word is bad and possesses a right-target violation. The simple three-case selectors have costs at most one: the `n<m` branch crosses the insertion by one symbol and the other branches have cost zero. The exact interface computation gives

    Good_0 = {epsilon},
    Good_1 = {0},
    Good_2 = empty.

The depth-one continuation starts with `0`, so an exposure-optimal selector certifies the entire original nonflat family.

## 4. Consequence for regular-middle erasure

Suppose a nonflat candidate family has a candidate-changing normalization whose image is a finite union of A016 fixed skeletons. Then arithmetic selector synthesis is no longer open:

1. decide exact reduced witness existence;
2. on each NO skeleton synthesize the minimum-cost selector of Theorem 3;
3. apply the finite lift check of Theorem 2.

This isolates the genuinely new obligation as obtaining a finite existence-preserving erasure cover and handling the interaction types that have no bounded right-target selector.

## 5. A genuine decidable nonflat class

Consider families represented as a finite union of triples

    (fixed reduced skeleton S, regular return-middle L, insertion anchor a)

with reconstruction `A_n M B_n`. Assume all accepted originals are covered by these triples. If, for each triple, either:

* the reduced skeleton has a witness and a stated witness-reflecting reconstruction condition produces an original witness; or
* the reduced skeleton is NO and Theorem 3 plus the finite compatibility check succeeds,

then the original family is decidable by finitely many Presburger and finite-automaton computations.

This is genuinely nonflat: `L` may be the full return language of a productive SCC and contain arbitrarily long recurrent paths. The theorem does not bound their number or length.

The current branch mechanically discovers SCC return languages, checks the return-state condition, computes compatible bounded prefixes, synthesizes constant-from-end selectors, and gives the exact finite simple-spine cover described separately in `2026-09-08-loop-erased-spine-cover.md`.

## 6. What remains

For arbitrary simple-spine return variables, the difficult selector interactions are now quite specific:

* every available violation may have its target cut before a recurrent insertion;
* one-sided exposure may be unbounded;
* the target suffix itself may contain a return variable that is absent or shifted in the source copy;
* two return variables may interact in the same comparison; or
* both compared occurrences consume the same recurrent word at different offsets, requiring literal shared-word reasoning rather than a finite prefix summary.

The next abstraction should classify these interaction types across the finitely many return variables of a loop-erased spine. Completely-after and bounded one-sided cases are solved above. Cases where both occurrences consume the same return variable should feed the A017 shared-word backend. A complete termination/coverage theorem for the remaining interaction graph is still open.
