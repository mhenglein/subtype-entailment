# Rational counting for terminal one-flag existence

Date: 2026-09-09. Read the [proof and exact limits](../notes/2026-09-09-one-flag-counting.md)
and [end-to-end route outline](../notes/2026-09-09-one-flag-route-outline.md).
Written proofs with reproducible checks; independent mathematical review pending,
not Lean-checked. This does not decide unrestricted Problem 1.7.

## Canonical claims

<a id="c065"></a>
### C065 - A complete terminal one-flag decision and computable witness bound

For every k-state binary partial deterministic terminal instance with at most
one forbidden ordered pair, witness existence is decidable. Arbitrary Bad sets,
initial/source states and multiple terminal accepting states are included.
For k>=2, a positive instance has a witness of length at most

    [k(k+1)/2]*(k+1)^k + k-2.

After source normalization, each candidate has at most one forbidden period.
The series counting accepted words and the series counting period incidences
are rational with a common effective denominator. Their difference counts
witnesses exactly. Its numerator degree is below m*k*(k+1)/2, where m is the
completed transition-monoid size. This gives a complete finite zero test rather
than an assumed search bound. The method also applies to single-source sets
of mutually unreachable distinct productive targets.

**Status:** WRITTEN PROOF + REPRO; independent review pending. The global
multi-flag problem is not decided. Nonregular witness languages are allowed.
[Proof](../notes/2026-09-09-one-flag-counting.md),
[implementation](../experiments/one_flag_counting.py).

<a id="c066"></a>
### C066 - Two targets defeat uncorrected incidence subtraction

A seven-state acyclic instance accepts exactly 0000 and 0110. With flags
(0,1) and (0,2), the first word has two forbidden periods and the second is a
witness. Accepted-word and period-incidence series are both 2*z^4. Their
identically zero difference is therefore not the true witness series z^4.
This refutes the direct multi-target extension of first-moment subtraction,
not the one-flag theorem, higher joint-incidence methods, or decidability.

**Status:** WRITTEN COUNTEREXAMPLE + REPRO; no minimality claim.
[Explicit table and proof](../notes/2026-09-09-one-flag-counting.md).

## Canonical experiment

<a id="e042"></a>
### E042 - Exact one-flag coefficient and decision regression

**Command:** `python3 experiments/check_one_flag_counting.py`

**Evidence:** all 2,304 three-state table/flag pairs, 320 four-state cases,
300 complete acyclic-language oracles, 111,413 word checks, 1,831 direct length
coefficient checks and independent determinant identities. Explicit infinite
positive/negative fixtures, the other agent's six-state extremal witness,
a nonregular witness-language family and the two-target cancellation are
retained. Unsupported inputs and deliberate caps do not become NO.

[Checker](../experiments/check_one_flag_counting.py),
[result](../results/one-flag-counting.json).

## Remaining mathematical question

For arbitrary targets, compute joint-period incidence series for the SAME
candidate word, or find a disjoint bad-word decomposition with an effective
zero test. Single-target counting does not establish those higher intersections.
Source-wise decisions also do not automatically compose across distinct sources.
