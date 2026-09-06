# Literature boundary for the continued alignment attempt

Date: 2026-09-06. This is a source check, not a proof or reduction.

The strongest newly checked external result is Havlena, Hecko, Holik and
Lengal, *Negated String Containment is Decidable*, technical report
arXiv:2506.22061v2 (revised 2025-06-30):
https://arxiv.org/abs/2506.22061
https://arxiv.org/pdf/2506.22061

The paper's Theorem 28 decides ONE not-contains constraint between two finite
concatenation terms, whose variables have regular membership constraints.
Theorem 29 adds chain-free word equations. Section 8 explicitly leaves
multiple not-contains constraints for future work. Its proof uses fresh
primitive factors in nonflat regular languages and a reduction to flat cases.

This does not immediately decide BorderAvoid. Our condition quantifies over
all pairs of internal positions, retaining the DFA states at both starts.
No transformation of those unbounded state-typed suffix obligations into one
of the paper's finite one-predicate instances has been supplied. Merely
writing the obligations as a conjunction of negated containments would not
satisfy the checked theorem's scope. No undecidability conclusion follows
from that failure either. A complete state-preserving reduction would remain
valuable research, but it must be proved rather than assumed.

The PDF's parsed theorem and future-work statements were inspected. An
attempt to obtain a web-rendered screenshot returned an internal error; no
visual PDF inspection is claimed. No text was treated as a substitute for
unseen tables or figures in deriving these scope statements.

For C055, the separate primary source Fernau, Hoffmann and Wehar, *Finite
Automata Intersection Non-Emptiness: Parameterized Complexity Revisited*
(2021), https://arxiv.org/abs/2108.05244, Section 1 p.2, records NP-completeness
for unary input alphabets. Our use is explicitly unary-DFA intersection,
followed by a polynomial reduction to the run-bounded terminal problem.
The unrestricted binary intersection PSPACE theorem is not an NP result.

No literature-priority claim is made for the new run-normalization or
prefix-monitor constructions. This bounded source check is not evidence
that no equivalent result exists elsewhere.
