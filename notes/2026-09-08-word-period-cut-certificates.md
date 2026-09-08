# Fixed-word-period three-way cut certificates

Date: 2026-09-08. Continues the arithmetic cut-selector route.

**Status: written proof + exact finite verifier; integrated regression pending
final CI replay at this commit; independent mathematical review pending; not
Lean-checked. Unrestricted Problem 1.7 remains open.**

## 1. From unary powers to word powers

The previous rules use two unary powers `a^n` and `a^m`. The arithmetic proof
only needs a repeatable word whose block boundaries can be tracked by finite
control. Let `P` and `B` be fixed nonempty binary words and let `M` be a regular
middle language. Consider a boundary-normalized terminal candidate language

    P^n B M P^m B P,     n>=0, m>=1.

The verifier checks this candidate-language equality exactly using the original
DFA and a finite epsilon-NFA for the displayed family. It also checks

    M subseteq {epsilon} union P Sigma*.

Thus an empty middle is allowed, while every nonempty middle begins with one
whole copy of P.

## 2. Finite block actions

Write `tau_P(q)=delta(q,P)` and `tau_B(q)=delta(q,B)`. Powers of `tau_P` have a
finite orbit on the automaton state set. The verifier requires all positive
leading `P`-powers to be defined and to share one `B`-anchor `q0`. It computes
the finite set of actual middle effects `q` by a product of the supplied middle
DFA with the terminal automaton.

For each effect `q`, every positive `P`-orbit state `r` must satisfy

    delta(r,BP)=final.

This is the fixed-word analogue of the unary terminal-cap condition.

## 3. Exact cut proof

Fix a candidate `w = P^n B u P^m B P`, with middle effect q.

- If `n<m`, put `d=m-n>=1` and `r=delta(q,P^d)`. The suffix at r is
  `P^n B P`. The source begins with the same word because after `P^n B` the
  middle is empty or begins with P. A flag `(start,r)` gives a violation.
- If `n=m`, the suffix at q is `P^n B P`, so `(start,q)` gives a violation.
- If `n>m`, put `d=n-m>=1` and `s=delta(start,P^d)`. The source suffix at s
  and target suffix at q both expose `P^m B P`; `(s,q)` gives a violation.

The cases are exhaustive. Only finite positive P-orbits and the finite set of
middle effects are required, so `VERIFIED_NO` is an all-length certificate.

## 4. Strict non-unary fixture

The regression uses

    P = 01,    B = 1,    M = {epsilon},

and an automaton accepting exactly

    (01)^n 1 (01)^m 1 01,   n>=0,m>=1.

The leading P-action loops at state 0. After the first delimiter, a one-shot
entry state forces the mandatory first P and reaches the recurrent trailing
P-boundary. This distinction is necessary: an earlier fixture reused the same
state before and after the first P and accidentally accepted the `m=0` word
`1101`; CI caught that fixture error before publication.

In the corrected automaton the exact verifier sees:

    leading P-orbit = {0}
    middle effect   = 2
    trailing P-orbit= {4}
    required flags  = {(0,2),(0,4)}.

The first flag handles equality and the `n>m` leading-orbit case; the second
handles `n<m`. The installed unary three-way, orbit-split and bi-residue
recognizers are required to remain inconclusive. Thus the theorem is genuinely
about a non-unary period, not a renamed unary run.

## 5. Significance and next step

The arithmetic certificate is stable under nontrivial fixed word periods. The
next abstraction is a **shared period variable with regular constraints**, not
merely a transition-action class. Replacing literal P by arbitrary words with
the same finite action would be unsound: the repository already has residual
collisions where equal actions have incompatible literal left contexts.

A safe generalization must retain one common word assignment across all powers
and cut comparisons, or provide an exact finite cover of possible periods. This
is where the shared-word equations and the transition-monoid/factorization-
forest machinery for 1-use backreference matching become directly relevant.
Lifting those per-word techniques to regular-language containment remains the
larger missing theorem.

## 6. Reproduction

Run

    python3 experiments/check_word_period_cut_certificate.py

[Verifier](../experiments/word_period_cut_certificate.py) ·
[checker](../experiments/check_word_period_cut_certificate.py).
