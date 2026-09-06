# Run normalization: proposed C054-C055 / E035

Base: PR #9 (`df54d87`). Date: 2026-09-06.
**No unrestricted Problem 1.7 decision is proved.** New statements have written
proofs and reproduced tests; independent review and Lean verification remain
outstanding. These are proposed continuation records, not a promotion of the
previous reductions to formalized theorems.

<a id="c054"></a>
## C054 - Exact profile-preserving normalization for every terminal word

For any defined binary word w ending at a terminal accepting state of a
k-state partial DFA, let r be its number of maximal homogeneous runs. There
is a constructible no-longer accepted word v with the same run-letter sequence,
the same states at all run boundaries, the same visited-state set, and

    A(v) = A(w).

Here A includes every state-pair suffix agreement, including diagonals and
empty suffixes. Thus every flag relation and every Bad annotation is preserved,
not only the annotations of a chosen witness. No marker or token format is
assumed and no delimiter is inserted.

Put H=(k+1)^2. For each bit, take the LCM of the eventual unary-cycle lengths
reached from its actual run starts; let P be the larger of the two LCMs. Then

    |v| <= r^2(H+P),
    P <= min(lcm(1,...,k), k^r).

The construction compresses gaps between sorted distinct counts, separately
for each letter, preserving small differences, large-difference residues,
order and equality. Synchronized unary pair-state sets stabilize after H
positions. A target's last run has length at most k-1, and its earlier source
may finish partway through a longer run; retaining that inequality is essential.

The same formulas give a polynomial-time exact witness verifier for binary-
encoded run-length descriptions. This bounds run lengths, NOT run count.

<a id="c055"></a>
## C055 - NP-completeness with a supplied unary run bound

Given an arbitrary explicit binary terminal Instance and R IN UNARY, deciding
whether a witness with at most R runs exists is NP-complete. Membership uses
C054's binary-encoded bounded counts and exact symbolic verifier. Hardness
reduces positive unary-DFA intersection using entry/interior flags to enforce
equal lengths in r blocks; every compiled witness has exactly 2r runs.
The source NP-completeness fact is attributed in the full proof.

For each FIXED R the bound using k^R gives polynomial-time enumeration, with
degree depending on R (XP, not an FPT claim). The implementation returns YES,
NO_WITHIN_RUN_BOUND, or UNKNOWN. The middle verdict is not unrestricted NO.

[Full statements, proofs and source attribution](../notes/2026-09-06-run-normalization.md).

<a id="e035"></a>
## E035 - Reproduction

```sh
python3 experiments/check_run_normalization.py
python3 experiments/run_experiments.py
```

[Symbolic profile and normalization](../experiments/run_normalization.py),
[bounded search and unary compiler](../experiments/run_bound_decision.py),
[checker](../experiments/check_run_normalization.py),
[saved result](../results/run-normalization.json).

The final seeded run checks all 256 three-state terminal tables and 780 accepted
short words; 1,974 further short words; all 288 complete unary transformations
through four states; 135,535 gap comparisons; 26,136 tail-pair comparisons;
344 expanded longer words and 216 huge-count words; 480 bounded-run questions
against complete acyclic-language oracles; 1,296 unary-DFA pairs and 20,736
block vectors; two exact canonical paths and six counting-family formulas.
A deliberate cap remains UNKNOWN. Huge encoded words were not expanded;
their symbolic checks are not independent letter-level tests at that scale.
The original core regression reproduces its committed output byte-for-byte.

## Revised frontier

The prior counting family has exactly (d+1)(d*2^d+2) runs in its unique witness,
on at most 18d^2+11d+3 states. Hence a polynomial run-count bound is unavailable.
A computable larger bound would combine with C054 to decide terminal existence,
but no such bound or complete unbounded-run method is proved here. Merely
increasing R remains a positive semiprocedure. Q002 and Q003 remain refuted.
