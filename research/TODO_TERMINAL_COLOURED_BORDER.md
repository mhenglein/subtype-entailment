# Next target: terminal coloured-border small model

Goal: prove any computable function `F(k)` such that every positive terminal `k`-state BorderAvoid instance has a witness of length at most `F(k)`.

Do **not** assume a polynomial bound, `k-2` budget, strict descent, constant edit count, or polynomial-size fixed skeleton; those routes have explicit counterexamples elsewhere in the repository.

Use the exact terminal bad-language decomposition:

- non-overlap violation = one earlier copy of the terminal suffix;
- overlap violation = periodic terminal pattern with exponent at most `k-1`.

Primary proof attempt: generalize the Anderson unbordered-word pumping argument to state-coloured source/target flags while carrying only these two violation forms. The existing forward-closed target theorem is rank-zero evidence, not the general case.

Alternative: decide directly whether a regular candidate language is contained in the finite union of the two bad-language families.

Required safety checks for any proof:

1. Preserve the source and target run-state colours, not just word borders.
2. Handle empty-suffix, diagonal, and Bad-state failures separately.
3. Never identify suffixes solely from equal automaton states or transition actions.
4. Do not turn a bounded overlap exponent into a bound on the gap word.
5. Do not assume generic existential word-equation decidability handles the universal choice of internal cut.
6. Resource caps are `UNKNOWN`, never negative certificates.

Start from [the decomposition proof](../notes/2026-09-07-terminal-bad-language-decomposition.md) and the earlier [forward-closed Anderson adaptation](../notes/2026-09-05-source-border-anderson.md).
