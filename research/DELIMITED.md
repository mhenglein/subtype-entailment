# Delimited-convolution continuation: proposed C051-C053 / E033-E034

Base: PR #8 (`c73f5af`). Date: 2026-09-06.
**Unrestricted Problem 1.7 is not settled.** New proofs are written and tested,
not independently reviewed or Lean-checked.

## Proposed claims

<a id="c051"></a>
### C051 - Necessary-budget emptiness is not a complete NO method

A five-state, three-flag flat binary terminal instance has no witness, while
Necessary(L,D) is nonempty for every finite L,D. Its candidates are
`1^n 0 1^m 0`, n>=0,m>=1, all excluded by three inequality cases. The word
`1^n 0 1^(n+1) 0` has one violation, of suffix length n+1 and gap n+2.
It passes exactly when n+1>L and n+2>D. C030 realizes this entailed query
with 11 subtype variables and 13 satisfiable normalized constraints.
This does not undermine the soundness of individual necessary certificates.

<a id="c052"></a>
### C052 - Exact arbitrary-flag bounded-block decision

For r supplied delimited regular data blocks with arbitrary flags/Bad on their
logical states, a reverse padded-convolution machine is exact. It retains
pairwise equal-tail bits and persistent flag-hit bits, then evaluates the
whole-block context guards. With b=binom(r,2) and P=product(n_i+1), at most
P*2^(2b) states suffice, and a positive binary witness of length at most
2r(2b+1)P exists. This construction-defined problem is PSPACE-complete,
including nonflat stage DFAs. Encoding uses 10/11 data and 00 delimiters;
helper states do not carry annotations. This is not an unrestricted encoding.

<a id="c053"></a>
### C053 - Automatic complete cover for a certified raw-input class

A raw binary terminal instance is checked for either a paired 10/11-versus-00
format with boundary-only flags, or a unary 1-versus-0 format. The certificate
requires that every boundary-safe accepted word follows the format and no
productive macro cycle contains a marker. Enumerating the finitely many
marker-edge sequences yields a complete C052 schema cover. Thus a checkable
nonflat class has an exact decision without a supplied decomposition. For k>=2,
a coarse positive-witness length bound is 2*k^3*(k+1)^k. Unsupported formats,
marker cycles, and caps give UNKNOWN. The direct five-state C051 input is
proved NO by two schemas. No markers are inserted into the input words.

[Full definitions, all-length proofs, limits, and source attribution](../notes/2026-09-06-delimited-convolution.md).

## Experiments

<a id="e033"></a>
### E033

`python3 experiments/check_delimited_blocks.py`

[Code](../experiments/delimited_blocks.py),
[checker](../experiments/check_delimited_blocks.py),
[result](../results/delimited-blocks.json).

470 complete finite-language schema oracles; 180 additional cyclic schema
checks; 4,096 independent DFA-product comparisons; 40,634 direct formula/binary
checks; 22 exact canonical path checks across both portions of the suite.
C051 also has 3,600 predicate identities, 100 exponent vectors, and 25 complete
necessary-graph searches, all nonempty. The all-budget conclusion is proved
separately. Deliberate caps remain UNKNOWN.

<a id="e034"></a>
### E034

`python3 experiments/check_marker_certificate.py`

[Front end](../experiments/marker_certificate.py),
[checker](../experiments/check_marker_certificate.py),
[result](../results/marker-certificate.json).

400 acyclic raw instances with every candidate enumerated; 160 cyclic schema
comparisons; 120 independent whole-word product comparisons. All 680 completed
without mismatch. Four unsupported-format fixtures and one cap preserve UNKNOWN.
A literal delimiter-insertion counterexample prevents claiming general coverage.

## Remaining target

Control unbounded/unaligned occurrence offsets without assuming a delimiter
structure. Neither a generic existential word-equation solver nor an increasing
sequence of necessary budgets supplies that completeness proof. See the exact
failure and preserved scope in the full note.
