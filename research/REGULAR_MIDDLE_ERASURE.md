# A012/A017 continuation: regular-middle erasure

Date: 2026-09-08. Base main: `18d9f9ad4f342c9ebf8c552f531a0d7f5feaf698`.

**Written proof + independent finite regression. Independent mathematical review pending; not Lean-checked. Unrestricted Problem 1.7 remains open.**

## Result

The six-state nonflat NO benchmark from the synchronized-tail regular-decoration barrier admits a genuine **candidate-changing normalization**.

Every accepted word has the form

    0^n 1 M 0^m 10,
    n>=0, m>=1, M in (0^+11)*.

Delete the arbitrary recurrent middle `M`:

    0^n 1 M 0^m 10  ->  0^n 1 0^m 10.

The middle is a loop from state 2 back to state 2. More importantly, the existing `n<m / n=m / n>m` forbidden-comparison selector lifts from the erased core back to every original word. In the only branch that touches the post-initial boundary, it needs only the first symbol of `M`, and every nonempty `M` begins with `0`; the empty case is handled by the first zero of the final run.

Thus an arbitrarily long genuinely nonflat productive region can be discarded modulo a proof-relevant interface. This is outside the candidate-covering regular-decoration model refuted by the previous barrier.

## Evidence

[Full proof and proposed reusable rule](../notes/2026-09-08-regular-middle-erasure.md).
[Independent checker](../experiments/check_regular_middle_erasure.py).
[Deterministic expected output](../results/regular-middle-erasure.json).

The checker exhausts all 32,767 binary words through length 14 (262 accepted, all parsed and certified, zero witnesses) and 6,240 structured candidates, including 6,084 with nonempty recurrent middles and words through length 42.

## Reusable direction

The proof suggests a `comparison-isolated middle` rule. A regular middle language can be erased when it returns to the same boundary state and every selected violating comparison avoids its interior except for a fixed common finite prefix. Those interface properties are regular-language questions; the missing part is a complete search/coverage theorem that finds enough selectors and erasable middles on every NO instance.

This is a new negative-certificate/normalization primitive, not a complete calculus and not a decidability proof.
