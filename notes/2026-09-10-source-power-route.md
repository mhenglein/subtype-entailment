# Source-power route outline

Date: 2026-09-10. Base f85ba3af769041349979e6130f1e2bc109b07c91.
Status: proposed proof route; evidence levels updated in its companion note.

Exact intermediate target: decide whether a supplied finite sequence of
source-simple cycle phases has a witness. A phase repeats one unknown
first-return word arbitrarily many times. Source-free paths between the
specified source positions remain arbitrary regular words. This is not a
finite-bound source-visit search or an arbitrary-input decomposition theorem.

Proposed chain:
1. A first-return word B at p generates exactly the p-loop words commuting
   with B. Thus U B=B U and a regular p-loop constraint mean U=B^m.
2. At boundaries of B^m Y, matches contained in the periodic prefix are
   detected at the earliest boundary. Every other match uses B^j P, where
   P is a nonempty border of Y. Write Y=Q P.
3. Its exact equality is B^j Q=D B^j, with target state delta(p,D).
   If Q=A B^ell with maximal ell, j<=ell is a finite-orbit condition,
   j=ell+1 is one exceptional conjugacy, and larger j adds no new target
   state beyond j=0.
4. Terminal capture enumerates all borders of Y by finitely many regular
   languages. A two-state-coordinate DFA tests all B-boundaries without
   knowing B's letters: its reference coordinate returns to p only there.
5. These clauses are positive existential word equations with regular
   constraints, sharing B,U,Y across all comparisons. Rotate a source-simple
   cycle to cover each internal source. Conjoin all phases and interfaces.
6. The constrained-word-equation decision theorem decides this supplied
   power scheme. It does NOT synthesize a finite complete cover for general
   inputs. Such existence-preserving coverage remains the global obligation.

Falsification: test the conjugacy reduction independently on all small word
pairs; then compare every boundary-origin comparison against the forward
predicate for loop/tail paths and arbitrary target sets. Ground the existential
formulas and check them with the optional string backend; do not interpret its
caps as a mathematical NO. Preserve non-first-return and omitted-exception
counterexamples. No external theorem is used to excuse a missing implication.

Opposing route: unchanged commuting loops do not implement independent PCP
accumulators. A failed global cover may instead expose changes between loop
words that can implement a real transformation; no such reduction is claimed.
