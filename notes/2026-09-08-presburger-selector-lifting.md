# Presburger selectors and lifting through regular return insertions

Date: 2026-09-08. Workstreams A012/A016/A017. Follows the regular-middle erasure and loop-erased-spine continuations.

**Status:** written consequences of the existing A016 fixed-skeleton translation plus finite regular-middle lift lemmas. Not Lean-checked. They give decidable nonflat subclasses, not unrestricted Problem 1.7.

## 1. Selector synthesis inside a fixed skeleton is complete

Fix one A016 skeleton

    s0 u1^n1 s1 ... ud^nd sd,    n1,...,nd >= 0.

Let `A(n)` say that the exponent vector produces an admissible accepted candidate. A016 already gives Presburger formulas for total length `N(n)`, state `c_n(x)`, letters at symbolic positions, and the exact witness condition.

Define the proper violation relation

    V(n,i,j) :=
      A(n)
      and 0 <= i < j < N(n)
      and G(c_n(i),c_n(j))
      and forall h (0 <= h < N(n)-j -> letter_n(i+h)=letter_n(j+h)).

Every atom is Presburger, hence `V` is effectively Presburger-definable. A fixed total order on cut pairs gives a canonical `LeastV` selector by excluding earlier violating pairs.

**Theorem 1 (fixed-skeleton selector).** The graph of a canonical violating-cut selector is effectively Presburger-definable. The supplied skeleton is NO exactly when every admissible exponent vector has a selected violation. This is decidable. Hand-written arithmetic branches are explanatory certificates, not a completeness requirement for selector synthesis.

## 2. One regular insertion: exact bounded-exposure lifting

Write a reduced candidate as

    r_n = A_n B_n

with insertion boundary `a(n)`. Insert arbitrary `M` from a fixed regular language `L`:

    w_(n,M) = A_n M B_n.

Assume every `M in L`, read from the original DFA state at the boundary, returns to that same state. `regular_middle_interface.py` checks this exactly.

For a reduced violation at `i<j` satisfying `i<a<=j`, lift the target to `j'=j+|M|`. Its suffix remains literally `r[j:]`, with length `ell=N-j`. The only changed part of the source's first `ell` symbols is after the insertion boundary. Define

    d = max(0, i + ell - a).

For fixed `d`, a word `P` of length `d` is **L-compatible** iff

    prefix_d(M P) = P    for every M in L.

This is a finite regular-language property. `good_reduced_prefixes` computes it exactly by combining the finitely many accepted middles shorter than `d` with the finitely many length-`d` prefixes extendable to an accepted middle.

**Theorem 2 (one-insertion lift).** If every middle returns the boundary state and the reduced continuation's first `d` symbols form an L-compatible word, then the reduced violation lifts through every `M in L`. If the possible exposure depths are bounded, all required compatibility checks are finite. Exposure boundedness and the exact maximum are Presburger-decidable.

## 3. Exposure-optimal selector synthesis

A fixed lexicographic selector can choose an unnecessarily difficult violation. Relative to one insertion, call a violation finite-cost when its target cut is not before the insertion:

* `a<=i<j`: cost 0; insertion is before both cuts and lifts for free;
* `i<a<=j`: cost the exposure `d` above;
* `j<a`: unresolved by this rule, treated as infinite cost.

For finite `c`, `CostV(n,i,j,c)` is Presburger. So is the graph of the minimum finite cost among all violations of one reduced word.

**Theorem 3 (exposure-optimal selector).** It is decidable whether every bad member of a supplied fixed skeleton has at least one finite-cost violation. On that domain it is decidable whether the minimum costs are uniformly bounded and, if so, their exact maximum. A Presburger selector can choose a minimum-cost violation and a deterministic tie-break. Combining this with the finite `Good_c` tests gives an exact NO certificate for the corresponding regular-insertion family.

This is strictly stronger than committing to `LeastV` first.

## 4. Multiple insertions compose right-to-left

Now let a reduced fixed-skeleton candidate contain finitely many insertion anchors

    a_1 < a_2 < ... < a_s

and regular return languages `L_1,...,L_s`. Original candidates are obtained by independently inserting `M_t in L_t` at each anchor. Every `M_t` returns the DFA state at its own anchor to itself.

Take one reduced violation `(i,j)` with target length `ell=N-j`. Say it is **right-safe for the erased set** when

    a_t <= j    for every t.

Anchors at or before `i` are harmless: inserting there shifts both cuts equally and leaves both suffixes unchanged. For each anchor strictly between the cuts,

    i < a_t <= j,

put

    d_t = max(0, i + ell - a_t).

The reduced source continuation beginning at `a_t` has a definite symbolic prefix of length `d_t`; require it to lie in `Good(L_t,d_t)`.

**Theorem 4 (multi-insertion bounded-exposure lift).** If `(i,j)` is a reduced forbidden comparison that is right-safe for every erased anchor, and every between-cuts anchor satisfies its exact `Good(L_t,d_t)` condition, then `(i,j)` lifts to a forbidden comparison after arbitrary independent choices `M_t in L_t` at ALL erased anchors.

**Proof.** Insert the return words in descending anchor order. Before the first insertion the comparison is valid. Consider the next anchor `a_t`.

If `a_t<=i`, both current cuts shift by `|M_t|`; neither compared suffix changes.

Otherwise `i<a_t<=j`. All previously inserted anchors are to the right. By induction the current source prefix of length `ell` still equals the target suffix, and in particular its first `d_t` symbols after the current image of `a_t` equal the reduced continuation prefix used in the `Good` check. Inserting `M_t` leaves the target suffix unchanged because the target cut is to its right, and the exact `Good(L_t,d_t)` identity leaves those `d_t` source symbols unchanged. Earlier source symbols are untouched. Thus the same comparison remains valid. Continue to the leftmost insertion. Boundary-state return guarantees the flagged states at the shifted cuts. QED.

There is no independence assumption between the *effects* of insertions beyond independent language choices: the right-to-left induction is what makes the local finite prefix checks compose.

### Effective selector with many erased anchors

For a fixed finite erased set, define the interaction cost of a reduced violation as infinity if some anchor lies strictly after its target cut. Otherwise use, for example,

    C(i,j) = max { d_t : i < a_t <= j },

with empty maximum zero. The relation `C(i,j)=c` is Presburger because the number of anchors is fixed and each `d_t` is a linear/max expression. Hence minimum finite cost over all violations is Presburger-definable exactly as in Theorem 3.

**Corollary 5 (multi-insertion exposure-optimal class).** For a supplied fixed skeleton plus finitely many regular state-return insertions, it is decidable whether every bad reduced member has a right-safe violation whose minimum maximum exposure is uniformly bounded. If so, one can synthesize an exposure-optimal Presburger selector and decide all finite `Good(L_t,d_t)` obligations. When they hold, every reduced NO member lifts to a bad original member.

This is a genuine multi-SCC nonflat NO class. The inserted return languages may contain arbitrary productive cycles and words of unbounded length; only the selected comparison's exposure to each erased region must be bounded.

## 5. Positive direction and exact decision subclasses

For a NO certificate, lifting bad reduced members is enough. For a full YES/NO decision on a candidate-changing cover one also needs a witness-reflecting positive direction.

A particularly simple case arises from the loop-erased spine cover. Every return language contains epsilon. Therefore the literal simple-spine word (all return variables set to epsilon) is itself a valid original candidate. If that word is a witness, the original instance is immediately YES.

More generally, a finite erasure cover can keep selected recurrent regions as A016 arithmetic/shared variables and erase only the remaining regular return regions. If each reduced component is exactly decidable and:

* a reduced witness has a proved reconstruction to an original witness; and
* every reduced NO component has an exposure-optimal lift certificate as above,

then the original covered class is decidable.

The six-state decoration-barrier benchmark is of this form: erase the genuinely nonflat `Ret(2)` middle, retain the unary/arithmetic `n,m` structure, and solve the two-counter reduced core. Its required exposures are at most one; `Good_1={0}`.

## 6. Exact loop-erased spine cover changes the global representation

The companion note `2026-09-08-loop-erased-spine-cover.md` proves that every accepted word lies in one of finitely many templates

    Ret(q0) a0 Ret(q1) a1 ... a_(r-1) Ret(qr),

where the `q_h` form a simple accepting path and `r<k`. Thus an arbitrary accepting run never needs an unbounded NUMBER of explicit recurrent variables: at most `k` regular return variables suffice while retaining their literal contents.

This makes Corollary 5 applicable spine-by-spine after choosing which return variables to erase and which to retain symbolically. It also identifies the true hard residue.

## 7. Remaining interaction types

For a selected comparison and an erased return variable, the solved cases are:

* insertion before both cuts: harmless;
* insertion strictly between source and target, with bounded exposure: Theorems 2/4;
* all such insertions simultaneously: Corollary 5;
* a forbidden comparison entirely in a forced common tail: `common_suffix_selector.py`.

The unsolved cases are now specific:

1. every available violation has some erased anchor strictly after its target cut, so the TARGET suffix itself contains an arbitrary return word;
2. the best right-safe exposure is unbounded;
3. source and target consume the same return word at different offsets, requiring literal shared-word reasoning;
4. multiple retained return variables interact inside one comparison.

These are the cases that should feed the A017 shared-word / chain-free-string machinery next. No unrestricted termination theorem is claimed.
