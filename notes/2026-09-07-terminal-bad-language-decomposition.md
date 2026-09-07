# Terminal bad-language decomposition and containment frontier

Date: 2026-09-07. Base main: `7b9aa1dded97d1e5ab1550497594c1ac093b1733`.

**Status: written all-length argument + reproduced finite checks. Independent review pending. Not Lean-checked.** This note does **not** settle unrestricted Problem 1.7. It records the exact structure of every proper violation in a terminal binary BorderAvoid instance and isolates the remaining containment question.

## 1. Exact decomposition of proper violations

Let `I` be a finite partial deterministic binary automaton whose accepting states are terminal. Let `w` be an admissible accepted word, with run states `c(0),...,c(n)`. A proper forbidden comparison is a pair `i<j<=n` with `(c(i),c(j)) in G` and `w[j:]` a prefix of `w[i:]`.

Put `d=j-i` and `z=w[j:]`.

Exactly one of the following cases holds.

### Non-overlap: `d >= |z|`

Write `C=w[i+|z|:j]` and `x=w[:i]`. Then

    w = x z C z.

The first and final occurrences of `z` are equal by the violation condition. Conversely, any accepted factorization `w=x z C z` whose first and final `z` occurrences begin in a flagged state pair is a violation.

The associated state conditions are regular: `x` takes the start to the source state, the first copy of `z` follows a path from source to some intermediate state, `C` reaches the target state, and the final `z` reaches a final state. Thus the non-overlap bad language is a finite union, over finite state choices, of one-use terminal-copy patterns of the form

    A (B)_Z C \Z

with no material after the copied `Z`.

### Overlap: `0 < d < |z|`

The suffix-prefix condition means `w[i:]` has period `d`. Let `y=w[i:j]`, let

    |w[i:]| = e*d + r,   0 <= r < d,

and write `y=uv` with `|u|=r`. Then

    w = x (uv)^e u.

Terminal nonmerging bounds the number of full gap copies. The suffixes beginning at

    i, i+d, ..., i+e*d

form a proper-prefix chain. Their starting states are pairwise distinct: if two aligned starts merged, determinism would make the earlier run reach the terminal accepting state before the word ended. Therefore

    e + 1 <= k,

so

    1 <= e <= k-1.

For a proper overlap `|z|>d`, hence in the convention above the periodic part contains at least two aligned occurrences whenever the final partial copy is counted appropriately. Equivalently, every overlapping violation is a bounded-power terminal pattern whose repetition count is bounded solely by the number of automaton states. This is the same terminal nonmerging mechanism recorded in C038; the present decomposition packages it together with the non-overlap case.

Boundary failures remain separate regular conditions: visiting a Bad state, a diagonal flag, or a flag into the final empty suffix.

## 2. Consequence: one sharp containment problem

After ordinary boundary normalization, terminal witness existence is equivalent to asking whether the regular language `R` of admissible accepted candidates escapes the finite union of:

1. finitely many state-constrained one-use terminal-copy languages `A(B)_Z C \Z`; and
2. finitely many state-constrained bounded-period overlap languages with exponent at most `k-1`.

Symbolically,

    Witness(I) nonempty
      iff
    R is not contained in Bad_nonoverlap union Bad_overlap.

This is an exact equivalence. It is **not yet a decision theorem**, because no general algorithm is proved here for that special containment problem.

The previously established word-equation identity `w=x d z` and `d z=z t` is consistent with this decomposition. In the non-overlap case, `d=z C`; in the overlap case, the standard conjugacy/periodicity form yields the bounded-power representation above.

## 3. Why this is substantially narrower than generic string theories

The non-overlap component uses one captured word exactly once again, and the copied occurrence terminates the candidate. There is no arbitrary material after the copy. The overlap component uses only a bounded number (`<=k-1`) of copies of one gap word plus a prefix remainder.

This is strictly more constrained than arbitrary word equations, general regular expressions with backreferences, or generic unbounded two-output template composition. Existing undecidability results for richer string theories therefore do not transfer without an exact reduction preserving the terminal-copy discipline.

Conversely, existing decidability results for membership in one-use backreference languages or for selected negated-containment theories do not immediately prove the required regular-language containment result. The quantifier order here is: choose one candidate `w`, then forbid every state-constrained internal cut of that same `w`.

## 4. Primary next theorem

The clean constructive target is a terminal coloured-border small-model theorem:

> For every `k`, there is a computable `F(k)` such that, if a `k`-state terminal instance has a witness, it has one of length at most `F(k)`.

The bound may be enormous. Polynomial or even elementary growth is unnecessary for decidability. The modular synchronization family already rules out small polynomial bounds.

Two ingredients are now available:

* every overlapping forbidden comparison is a bounded-power pattern with exponent at most `k-1`;
* every non-overlapping forbidden comparison is a single earlier occurrence of the final suffix.

A promising route is to generalize the Anderson unbordered-word pumping argument from one forward-closed target colour to finitely many state-coloured sources/targets, using the terminal-copy/bounded-overlap decomposition instead of arbitrary border structure.

## 5. Finite reproduction

The accompanying checker replays this decomposition against the direct witness predicate. The recorded run covers:

* 852 terminal instances;
* 435,372 binary words;
* 2,630 admissible accepted candidates;
* 1,770 bad accepted candidates;
* 407 observed non-overlap violations;
* 22 observed overlap violations;
* zero decomposition mismatches;
* maximum observed overlap exponent 4.

Every observed overlap satisfies the proved `e<=k-1` bound. These counts validate the implementation only; the quantified decomposition rests on the all-length argument above.

No full repository CI, global link scan, or Lean build is claimed for this checkpoint.
