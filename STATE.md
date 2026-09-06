# Subtail - current research state

Updated: 2026-09-06

The unrestricted Problem 1.7 is not settled. Preserve arbitrary, possibly
infinite type-tree semantics, exact quantifiers, and proof/evidence levels.
This is compressed scientific memory, not a replacement for the linked proofs.

## Latest continuation: universal binary normal forms and run profiles

**Proposed C057-C059 (written proofs + E036, independent review pending):**
the uniform code 0->00,1->10 gives an exact 2k-state reduction preserving every
witness, with flags only at original-state boundaries. Thus the full terminal
problem is already present when all data-1 runs have length at most one and
nonempty words end in zero. Simple token structure is not a complete solution.

For ANY binary DFA, even with nonterminal finals and recurrent flag targets,
C058 contracts unary run lengths while preserving the exact full agreement
profile, visited states, and endpoint. If r counts occurrences of the last
letter and d counts distinct intervening run lengths, the new word length is
at most r[(k+1)^2+d(k+P)+1], with P the unary transition's cycle-period LCM.
The contraction preserves short differences, weak order and residues. It need
not be strict, and it does not bound r. A recurrent-target witness contracts
from 1,421 to 135 letters with exactly the same profile.

A computable existential bound on r would supply a general word-length bound.
But r can be superpolynomial even in C057's zero/one-run normal form, by the
existing modular family. The remaining sequence problem retains the full
expressive power of the original, not a known easy special case.

Last-final/last-bit slicing also extends C056's front end without new states
or markers. It resolves the former wrong-final-symbol format rejection, while
unresolved recurrent-target cycles still return UNKNOWN.

[Proposed claims/E036](research/RUN_PROFILES.md),
[proof and failed simplifications](notes/2026-09-06-run-profile-normalization.md),
[result](results/run-profiles.json). No independent review or Lean check.

## Previous continuation: target-free prefix saturation

**Proposed C054-C056 (written proofs + tests; independent review pending,
not Lean-checked):** the marker restriction is weakened. Productive marker
cycles are allowed before the first relevant flag target; only cycles reachable
from a target are excluded. A target is a SECOND endpoint of G, not a source.

For a fixed r-block reference suffix containing all targets of a witness, early
blocks are summarized by reference equality and equal-tail flag-hit subsets.
A pending-pattern monitor has at most K*2^(r-1) boundary memories, so deleting
repeated memories leaves at most K*2^(r-1)-1 early blocks with the SAME reference
suffix. This is G-specific witness preservation, not profile domination or
the refuted low-budget strict-descent theorem.

A powerset construction chooses the reference words and simultaneously keeps
all possible source-block observations relative to that same tuple. It closes
longer unmatched source prefixes by finite data reachability. The resulting
schema search is finite, with at most

    2*(K+1)^r * 2^(2*binom(r,2)+2*K^2*4^r)

states and an explicit computable witness-length bound. Under the raw-input
certificate, r<=K-1 and the reference schemas can be enumerated completely.
Candidates may still have unboundedly many early markers; the cover preserves
existence rather than imposing a false candidate-language bound.

Two fixtures allocated with 21 binary states (seven macro states, eighteen live
raw states) are decided YES and NO respectively, while C053 returns UNKNOWN
for both. E035 covers 160 complete acyclic oracles, 160 prior exact-schema
comparisons, 256 cyclic-prefix flag relations, exact source-observation tests,
and explicit normalization/scope/cap regressions. Main proof gap: target-reachable
marker cycles or the absence of an agreement-preserving token format.

[Proposed claims/E035](research/TARGET_FRONTIER.md),
[proofs](notes/2026-09-06-target-frontier.md),
[result](results/target-frontier.json).

## Previous continuation: exact convolution and a negative-method obstruction

**Proposed C051 (written proof + tests; independent review pending):** a
five-state, three-flag flat terminal instance has no witnesses although EVERY
finite Necessary(L,D) language is nonempty. Its candidates 1^n 0 1^m 0 are
excluded by n<m, n=m, or n>m. At m=n+1 the unique violation has suffix length
n+1 and gap n+2, escaping every fixed budget for large enough n. Thus increasing
necessary budgets is not a complete NO semiprocedure. Individual necessary
emptiness certificates remain sound. C030 gives an entailed query on 11
variables and 13 satisfiable normalized constraints.

**Proposed C052:** arbitrary flags/Bad on logical states of finitely many
regular delimited blocks are handled exactly by reverse padded convolution.
The memory retains equal-tail and flag-hit bits and delays the whole-block
context guards until the words finish. With b=binom(r,2), P=product(n_i+1),
there are at most P*2^(2b) states and a positive binary witness bound 2r(2b+1)P.
The supplied-schema problem is PSPACE-complete, including nonflat components.
This is not a general PSPACE upper bound.

**Proposed C053:** a raw binary terminal input can be certified automatically
for either a paired 10/11-versus-00 marker format with boundary-only flags,
or a unary 1-versus-0 format. All boundary-safe accepted words must follow the
format and no productive macro cycle may contain a marker. Enumerating marker
edge sequences then gives a complete finite schema cover. The direct five-state
C051 instance is proved NO by two schemas, despite all its necessary graphs
being nonempty. A coarse raw-state witness bound is 2*k^3*(k+1)^k for k>=2.
Unsupported formats and all caps retain UNKNOWN; no markers are inserted.

[Proposed claims/E033-E034](research/DELIMITED.md),
[full proofs](notes/2026-09-06-delimited-convolution.md),
[block checks](results/delimited-blocks.json),
[raw-input checks](results/marker-certificate.json).
All three results await independent review and are not Lean-checked.

## Previous structural results

C048-C050 (written proofs + tests, pending review) force equality of arbitrary
regular-constrained words using predecessor tags at encoded boundaries.
Their product-decided nonflat class supplies explicit PSPACE hardness for
terminal BorderAvoid and, through C030, normalized bottom/product entailment
and non-entailment, even on satisfiable systems. A polynomial-size counting
family has one witness with exponentially many short factors, ruling out
polynomial-size fixed-word skeleton and ordinary straight-line descriptions.
Larger effective covers and more expressive symbolic descriptions remain open.
[Records](research/WORD_SYNC.md).

C046 refutes Q002 (terminal k-2 budgets) and Q003 (strict profile descent above
k-2): an eight-state terminal example has exact budget seven and unique shortest
witness 11111101111110. More generally r modular unary blocks have exact budget
(r-1)(lcm(periods)+1). Periods 1,...,m give superpolynomial terminal budgets and
shortest words on quadratic-size inputs. The family is nevertheless decidable
by LCM and flat. C047 requires r coordinated loop deletions on 2r+1 states,
ruling out constant deletion counts. These statements are written/tested,
not independent-review or Lean results.
[Proof](notes/2026-09-05-modular-synchronization.md),
[claims](research/claims.md#c046), [Q002](research/conjectures/Q002.md),
[Q003](research/conjectures/Q003.md).

## Foundations and restricted decisions

The audited path-set/pushdown characterization supports regular countermodels
under its satisfiability premise. Several binary truncation/context lemmas,
direct budget predicates, reversal, and an exact two-state decision are
Lean-checked. The conditional budget theorem does not supply its global bound.

The implemented subtype-to-summary bridge has independent interface checks,
not complete all-input formalization. Written C023-C029 give absorption,
simplified denial safety, and a decision for infinitely extendable witnesses.
A negative answer for that category is not unrestricted entailment. C030
realizes arbitrary terminal instances on 2k+1 subtype variables; C031 connects
the terminal decision problem with the remaining normalized problem at the
recorded proof levels.

C033 decides flat terminal graphs by a complete Presburger skeleton cover.
C034 completes the four-state terminal census with audited graph code.
C035-C040 give nonflat obstructions, terminal nonmerging, bounded exponents,
and restricted pair/source certificates. C041-C045 provide exact reformulations
and local shortening lemmas, not the refuted global descent statements.

## Failed routes not to restart unchanged

The old regular prefix-reachability formula is false. Bounds on all rigid words
are false. Equal-state loop deletion is not automatically sound. Flat edge
restrictions can lose every witness. Source-local viability plus a cyclic
pair residual does not imply YES. Witness languages can be nonregular.

Also refuted: terminal k-2 budgets, unconditional strict descent above k-2,
polynomial witness/budget bounds, constant simultaneous deletion counts, and
polynomial-size fixed skeleton or ordinary straight-line witness descriptions.
Now additionally refuted: completeness of finite Necessary-emptiness
certificates. Delimiter insertion is not an agreement-preserving reduction:
the flagged terminal path 00 becomes valid after encoding/appending a marker.

## Current frontier

Control the unbounded sequence of run-length values and its later-block
suffix-equality guards. C058 gives a full-profile numerical contraction with
no recurrent-target restriction, but the number of blocks remains unbounded.
C057 shows the full terminal problem persists even when each data run has only
zero or one letters. A computable marker-count bound, or a different complete
representation of those sequences, is still missing.

The earlier target-frontier and convolution solvers remain exact within their
certificates. Last-bit slicing removes a representational failure, not the
recurrent-cycle obstruction. Generic finite-register word-constraint results
have not been shown to express all our arbitrary-distance suffix obligations.
Neither a finite two-run signature nor successful bounded tests establish an
unrestricted finite quotient or decision procedure.

A008/A017 track the new normal forms; A012 retains the incomplete necessary-
budget warning; A009 retains growth bounds; A011 tracks exact reductions;
A018 retains formal decision obligations. The [generated tracker](research/README.md)
holds execution status. Tests, written proofs and independent review remain
separate evidence levels.
