# Open research questions

Problem 1.7 remains unsolved. See [the current review](REVIEW.md) for definitions, proofs, and the detailed plan.

- [ ] Obtain the original `analysis-2026` scripts and reproduce the memo's census against the independent implementation.
- [ ] Integrate the stronger suffix-trace and incoming-flag-set truncation rules; examine shortest witnesses that resist them.
- [ ] Prove a computable bound on the minimum successful `L+D` budget, or refute specific proposed bounds with certified examples.
- [ ] Identify restrictions shared by summary automata derived from actual top-free subtype constraints.
- [ ] Complete the converse reduction if a result about arbitrary BorderAvoid is to be transferred back to subtype entailment.
- [ ] Develop complete NO certificates beyond the current bounded necessary-condition searches.

## Established starting points

- The memo's nonmerging interpretation of rigidity is false; the two-state `0^n` family is a counterexample.
- A stronger sufficient truncation rule and its flag-profile variant are proved in the review and implemented in `experiments/border_lab.py`.
- The singleton-word family has exact budget `n-1` at `n+1` states. It calibrates search generators but does not imply undecidability.

These statements concern the precise models described in the review. Do not transfer a result between finite trees, regular infinite trees, and arbitrary trees without a proof.
