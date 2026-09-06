# Subtail - current research state

Updated: 2026-09-06

The unrestricted Problem 1.7 is not settled. Preserve arbitrary, possibly
infinite type-tree semantics, exact quantifiers, and proof/evidence levels.
This is compressed scientific memory, not a replacement for the linked proofs.

## Latest continuation: exact convolution and a negative-method obstruction

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

Extend complete alignment/decomposition beyond the automatic bounded-marker
class, or find a different complete symbolic decision. C052 now handles all
logical flags once data tails align; C053 proves coverage without supplied
schemas for its explicit input certificate. It does not control marker cycles,
arbitrary unaligned flags, or all possible terminal inputs. A generic word-
equation solver does not discharge the universal internal suffix conditions.

A012 tracks complete NO certificates and C051's obstruction. A016/A017 track
finite representations and the convolution/cover machinery. A008/A009 retain
lower-bound and minimal-witness evidence; A011 tracks exact reductions; A018
retains formal decision obligations. The [generated tracker](research/README.md)
holds execution status. Do not promote tests or failed-certificate UNKNOWN
verdicts into an unrestricted conclusion.
