# Fixed-word-period three-way cut certificates

Date: 2026-09-08. Continues the arithmetic cut-selector route.

**Status: written proof + exact finite verifier; CI integration pending at this
commit; independent mathematical review pending; not Lean-checked. Unrestricted
Problem 1.7 remains open.**

## 1. From unary powers to word powers

The previous rules use two unary powers `a^n` and `a^m`. The arithmetic proof
only needs a repeatable word whose block boundaries can be tracked by the finite
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

Fix a candidate

    w = P^n B u P^m B P,

with middle effect q.

### n < m

Put `d=m-n>=1` and let `r=delta(q,P^d)`. The suffix at r is exactly

    P^n B P.

The source suffix from the start begins with the same word: after `P^n B`, the
middle is either empty, in which case the trailing power begins with P, or it is
nonempty and the verifier has proved that it begins with P. A flag `(start,r)`
therefore gives a violation.

### n = m

The suffix at q is `P^n B P`, and the same source-prefix argument applies.
A flag `(start,q)` gives a violation.

### n > m

Put `d=n-m>=1` and `s=delta(start,P^d)`. The source suffix from s begins

    P^m B P,

while the target suffix at q is exactly `P^m B P`. A flag `(s,q)` gives a
violation.

The three cases are exhaustive. Because only the finite positive `P`-orbits and
finite middle-effect set are needed, the verifier checks a finite flag set.
`VERIFIED_NO` is therefore an all-length certificate.

## 4. Strict non-unary fixture

The first regression uses

    P = 01,    B = 1,    M = {epsilon},

and an automaton accepting exactly

    (01)^n 1 (01)^m 1 01,   n>=0,m>=1.

Both P-actions are loops at their respective block-boundary states, so one flag
covers all three arithmetic cases. The installed unary three-way, orbit-split,
and bi-residue recognizers are required to remain inconclusive on this fixture.
Thus this theorem is not merely a renaming of a unary run.

## 5. Significance and next step

The arithmetic certificate is now stable under nontrivial finite word periods.
The next abstraction is to replace one fixed word P by a **regular transition-
monoid fibre**: repetition pieces may be different words with the same finite
action, while cut correctness must still preserve their literal shared content.
That is precisely where earlier residual-collision counterexamples warn against
forgetting the common word assignment. A safe extension will need either shared
word parameters or an exact finite family of period representatives justified
by the candidate-language cover.

This is also the point where the 2026 1-use backreference matching machinery is
relevant: its algorithms use transition monoids, factorization forests and word
periodicity for the canonical `A(B)_x C x D` problem. Lifting those per-word
techniques to regular-language containment remains unproved.

## 6. Reproduction

Run

    python3 experiments/check_word_period_cut_certificate.py

[Verifier](../experiments/word_period_cut_certificate.py) ·
[checker](../experiments/check_word_period_cut_certificate.py).
