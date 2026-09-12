# Source-visit bounds and closed-source-walk recovery

Integrated: 2026-09-12. Integration base: `52d5270342b27aee3cad10e1b2d0ac7d9307a580`.
Workstreams: A008 (integration history), A009, A017; question Q004.

**WRITTEN PROOF + REPRO. Independent mathematical review pending; not Lean-checked.
Problem 1.7 and the unrestricted existence-preserving cover remain open.**

This is the canonical claim/experiment supplement for both previously chat-only
bundles. It preserves the original proofs, source code, examples, limitations,
and integrity manifests. The original modular construction is C046, not a new
construction. The closed-walk compiler uses C071; its proof is a dependency,
not newly independently certified by this integration.

## Start here and reproduce

Read the [source-visit proof](../experiments/recovered_2026_09_12/subtail_source_visit_bound/RESEARCH_NOTE.md),
[closed-walk proof](../experiments/recovered_2026_09_12/subtail_closed_walk_lift/RESEARCH_NOTE.md),
and [end-to-end route](../experiments/recovered_2026_09_12/subtail_closed_walk_lift/ROUTE_OUTLINE.md).

From a clean checkout, using Python 3.10+ and no third-party packages:

```sh
python3 experiments/recovered_2026_09_12/reproduce.py
python3 scripts/research_index.py --lookup C075
```

The first command materializes both complete original bundles in a fresh
temporary directory and prints its location. The four large derived files
(`results.json`, `run.log`, `formula-example.json`, `witness-model.json`) are
regenerated, not duplicated in Git. Every original SHA256 and byte length is
verified. All 1,161 live-flag certificates, the expanded formula, and its
explicit satisfying assignment are recoverable without a network or this chat.
[Recovery instructions](../experiments/recovered_2026_09_12/README.md) and
[provenance](../experiments/recovered_2026_09_12/PROVENANCE.json) explain the layout.

Historical statements in the preserved bundle notes about unchanged remote
files or unallocated IDs describe their original delivery. This record supplies
the publication context and canonical IDs without rewriting that evidence.

## Claims

<a id="c073"></a>

### C073 — Exact source-visit lower bounds with live flags

**Statement.** In the existing C046 modular family with r>=2 positive periods
p_i, let L=lcm(p_i) and k=1+r+sum(p_i). The exact witness language is
`{(1^N0)^r : N is a positive multiple of L}` and the minimum flagged-source
visits over all witnesses is `(r-1)(L+1)`. Visits count positions, not labels.
If every earlier period is coprime to the last, every individual flag has an
accepted-word certificate of an actual forbidden comparison. Using all primes
at most x yields `log(min_visits)/sqrt(k*log(k)) -> 1` along that family.

**Status and dependencies.** Written derivation + reproducible finite checks;
independent mathematical review pending, not Lean. The language and automaton
are prior C046 work. The asymptotic uses the precisely sourced prime-number
estimates and partial summation in the preserved proof; no priority claim.

**Limit.** This excludes polynomial universal Q004 bounds, not arbitrary
computable bounds. The family is flat and has an exact arithmetic decision.
Large witnesses do not establish undecidability or a runtime lower bound for
symbolic existence decisions. The result is not a general upper bound.

**Evidence.** [Proof, definitions, liveness construction and sources](../experiments/recovered_2026_09_12/subtail_source_visit_bound/RESEARCH_NOTE.md),
[implementation and direct/reversed predicates](../experiments/recovered_2026_09_12/subtail_source_visit_bound/source_visit_bound.py), E046.

<a id="c074"></a>

### C074 — Exact counter lifts and whole-base power guards

**Statement.** For a supplied positive modulus d, the source-arrival counter
product preserves acceptance, safety and every forbidden comparison when flags
are lifted over all pairs of residues. A nonempty safe loop B at a counted
pivot with exactly d arrivals, excluding its start and including its endpoint,
is first-return in that lift; every counted-position rotation is too.
`UB=BU`, a safe original pivot loop U, and arrival count U divisible by d hold
together exactly when `U=B^m` for an integer m>=0.

**Status.** Written proof + finite regression evidence; independent review
pending, not Lean. No lexical primitivity or original first-return assumption
is imposed. The counter modulus is fixed from the supplied source walk, not
inferred as an unbounded unknown inside a finite automaton.

**Limit.** Lifting only equal-residue flags would erase genuine comparisons.
Commutation alone accepts fractional powers: B=1010 and U=10 are a preserved
regression. This is a local exact encoding, not a complete cover theorem.

**Evidence.** [Definitions and Lemmas 1-4](../experiments/recovered_2026_09_12/subtail_closed_walk_lift/RESEARCH_NOTE.md),
[compiler](../experiments/recovered_2026_09_12/subtail_closed_walk_lift/closed_walk_lift.py), E047.

<a id="c075"></a>

### C075 — Exact supplied closed-source-walk scheme compilation

**Statement.** Using C071, witness existence inside a supplied finite
closed-source-walk power scheme reduces to positive existential word equations
with regular constraints. A supplied base may revisit the same source label.
Its unknown positive segments have source-free interiors, its copy exponent
is unbounded, and all bases, bridges and suffixes share one assignment.
Phase-local counter lifts apply C074 and C071 to every rotated source
occurrence; empty powers do not require an inhabited base language.
The reduction is polynomial in the instance and explicit scheme. DGH Theorem 4
for free monoids with involution, restricted to binary words and concatenation,
gives a PSPACE upper bound for this supplied-scheme problem.

**Status and dependencies.** Written proof + reproducible compiler/certificate
checks; independent mathematical review pending, not Lean. C067/C071 and the
external word-equation theorem retain their stated evidence levels. Neither
their full proofs nor the subtype bridge are newly independently verified here.

**Limit.** The implementation compiles the exact formula; it does not implement
the complete external decision algorithm. A false supplied assignment is not
UNSAT. The number of phases and total listed base-source occurrences are not
bounded effectively from an arbitrary instance. Q004 and unrestricted Problem
1.7 remain open. No hardness or general PSPACE claim is made.

**Evidence.** [Compilation proof and exact theorem mapping](../experiments/recovered_2026_09_12/subtail_closed_walk_lift/RESEARCH_NOTE.md),
[route and remaining cover obligation](../experiments/recovered_2026_09_12/subtail_closed_walk_lift/ROUTE_OUTLINE.md),
[compiler](../experiments/recovered_2026_09_12/subtail_closed_walk_lift/closed_walk_lift.py), E047.

## Experiments

<a id="e046"></a>

### E046 — Source-visit lower-bound replay and live-flag certificates

**Command.** `python3 experiments/recovered_2026_09_12/reproduce.py` restores and
runs the original source bundle as well as E047. In its printed output directory,
`python3 source_visit_bound.py --self-test --output replay.json` can also be run
from the source bundle subdirectory.

**Coverage.** 40,955 raw binary-word comparisons; 2,384 exponent vectors;
3,476 complete accepted-path comparisons, including all 3,468 paths through
length 93 for the 14-state fixture; 1,161 individually checked live flags;
three materialized least witnesses and explicit boundary/loop-deletion cases.
The large prime rows are arithmetic consequences of the written formula,
not exhaustively searched words. The all-length conclusion is C073.

**Artifacts.** [Source and embedded bounds](../experiments/recovered_2026_09_12/subtail_source_visit_bound/source_visit_bound.py),
[original manifest](../experiments/recovered_2026_09_12/subtail_source_visit_bound/SHA256SUMS),
[output hashes and archive provenance](../experiments/recovered_2026_09_12/PROVENANCE.json).
The full certificate appendix and console log are restored byte-for-byte.
No seed is needed for this deterministic enumeration.

**Integration replay.** Original suite and full recovery runner passed on
2026-09-12. This is finite regression/integrity evidence, not independent
mathematical review, Lean verification, or unrestricted emptiness testing.

<a id="e047"></a>

### E047 — Counter-lift compiler and explicit positive-certificate replay

**Command.** `python3 experiments/recovered_2026_09_12/reproduce.py`. The original
checker uses seed 2026091217. The printed recovered directory contains all files
needed for `python3 verify_example.py` in its closed-walk bundle subdirectory.

**Coverage.** 22,950 projection words; 39,346 guarded-power comparisons with
1,605 fractional commuters rejected; 4,925 rotated first returns; 550 complete
phase queries and 1,228 lifted-boundary queries; grounded formulas, repeated
source labels, different phase moduli with common tails, and empty-star cases.
[Exact counts and limits](../experiments/recovered_2026_09_12/subtail_closed_walk_lift/checks.json),
[checker](../experiments/recovered_2026_09_12/subtail_closed_walk_lift/check_closed_walk_lift.py).

**Positive certificate.** The regenerated formula has 564 equations, 689 regular
atoms and 676 word variables. Its fixed assignment produces `1010110`, satisfies
the serialized Boolean formula, and passes both original witness predicates.
[Certificate verifier](../experiments/recovered_2026_09_12/subtail_closed_walk_lift/verify_example.py).
No SMT or complete word-equation solver was executed.

**Preserved failures.** Fractional commutation B=1010,U=10; one-flag interior
loop deletion `01001011001 -> 01001001`, introducing the flagged comparison
at cuts (0,3); the existing C071 exceptional-conjugacy word `010010101`.
The one-flag interior deletion does not refute valid first-to-last single-source
normalization. The original exploratory search log was not in the delivered
bundles; the explicit regression is complete and executable.

**Integration replay.** Both bundles' 14 manifest-listed files, including four
regenerated large outputs, matched every original SHA256. This is not an
independent mathematical review, Lean check, or a full local repository CI run.

## Research handoff

A008/A009: do not retry polynomial total-source-visit bounds. Distinguish total
visits from symbolic scheme cost: one short phase represents unbounded visits.
The C046 construction and existing flat-family solver are not new discoveries.

A017: independently audit the counter guard and C071 interface, especially
all-residue flags, shared tails, rotations and empty-star branches. Then attack
an existence-preserving computable bound on the number of phases plus total
listed source occurrences in the powered bases, or another complete symbolic
treatment of changing return words. No such bound is assumed by C075.

An opposing undecidability construction must escape the effectively bounded
scheme framework or invalidate a precise dependency. The trailing-context
pattern reduction does not supply an exact terminal-anchor reduction.
