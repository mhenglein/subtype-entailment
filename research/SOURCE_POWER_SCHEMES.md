# Exact source-cycle power schemes

Date: 2026-09-10. Base: `f85ba3af769041349979e6130f1e2bc109b07c91`.
Written proofs plus executable checks; independent mathematical review pending,
not Lean-checked. The complete original problem remains unresolved.

## Canonical claims

<a id="c071"></a>
### C071 - Eliminate every repeated source-boundary obligation

Let B be a nonempty safe first-return word at p, Y a safely terminal-accepted
word from p, and U=B^m for any m>=0. A finite positive existential formula of
word equations and regular constraints expresses absence of every forbidden
comparison sourced at the displayed boundaries of UY. Targets are unrestricted.
The words B, U and Y remain shared variables; neither the exponent nor the
base-word length is supplied or bounded.

Matches contained in a periodic prefix are caught at the first source. Every
other match leaves a nonempty border P of Y. With Y=QP and Q=A B^ell maximal,
the exact equation B^j Q=D B^j has three cases: j<=ell, j=ell+1, and j>ell+1.
A regular pair monitor checks the first case, one conjugacy checks the second,
and the third adds only the already-tested j=0 state. Terminal capture lists
all borders using at most k accepted-prefix variables. First-return structure
makes commutation plus a p-loop constraint express EXACT powers without
requiring lexical primitivity.

**Status / scope:** WRITTEN PROOF + REPRO. This checks the displayed repeated
source positions, not other origins; C072 covers all origins in its supplied
scheme. An explicit six-state example refutes omission of the exceptional case.
[Proof and exact formula](../notes/2026-09-10-source-power-schemes.md),
[concrete checker](../experiments/source_power.py),
[formula compiler](../experiments/source_power_formula.py).

<a id="c072"></a>
### C072 - Mixed-family existence for a supplied finite power scheme

A supplied phase scheme specifies finitely many ordinary source visits and
source-simple cycles (a cyclic list of distinct flagged-source labels). Each
cycle base is an UNKNOWN word, with arbitrary regular source-free paths between
its listed sources, and is repeated an UNBOUNDED number of times. Different
phases can have different bases. Rotations and C071 cover every source position;
all later tails use the same assignments. The resulting finite existential
formula is satisfiable iff SOME member of the scheme is a witness, including
when the family also contains invalid words.

The DFA-atom reduction is polynomial in the input and supplied scheme size.
The same free-monoid constrained-equation theorem used by C067 yields decidability
and a PSPACE upper bound. The optional regex/SMT implementation is not that
complete theoretical algorithm and may return UNKNOWN.

**Status / scope:** WRITTEN PROOF + REPRO; not a finite complete cover of arbitrary
instances. No bound on the number of phases or replacement of changing return
words by identical copies is established. Q004 remains open. This is synthesis
within a supplied family, not merely universal verification of that family.
[Proof and external theorem mapping](../notes/2026-09-10-source-power-schemes.md),
[end-to-end outline and remaining obligation](../notes/2026-09-10-source-power-route.md).

## Canonical experiment

<a id="e045"></a>
### E045 - Source-power identities, boundary checks and compilation probes

**Commands:** `python3 experiments/check_source_power.py`;
optional `python3 experiments/check_source_power.py --with-smt`.

The deterministic run checks 173,910 power-conjugacy identities, 2,404 loop/tail
contexts, 14,424 direct/reversed boundary-set comparisons, 56,896 return-word
commutation cases, 2,097 rotations, 81 complete two-cycle profiles and six exact
canonical-model paths. Huge-exponent checks use a proved symbolic threshold;
they do not expand words with 10^60 repetitions.

The optional 28 probes record 5 SAT, 10 UNSAT, 13 UNKNOWN on the saved run.
All six larger two-cycle formulas and both free-exponent probes remain UNKNOWN.
Two grounded one-phase witnesses are reconstructed and verified. These timed
outcomes are not a deterministic CI oracle; solver UNSAT is not a checked proof.
The complete theoretical compilation rests on its written proof, not on a
claim that these incomplete backend probes decide every scheme.

[Checker](../experiments/check_source_power.py),
[deterministic result](../results/source-power.json),
[optional backend result](../results/source-power-smt.json).

## Remaining question

Construct an effective finite existence-preserving cover by such schemes, or
handle genuinely changing loop words by another terminating method. Enumerating
more schemes without a completeness bound is still only a positive search.
