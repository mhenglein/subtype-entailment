# Regular-family validation: PSPACE classification and orbit backend

Date: 2026-09-07. Workstream: A017. Consolidated claim: C062.

**Status: written proof plus executed regression evidence; independent review pending; not Lean-checked. This does not settle unrestricted Problem 1.7.**

## 1. Problem

For a binary BorderAvoid instance `I` and an unannotated binary DFA `D`, ask:

> Is every word in `L(D)` a witness of `I`?

This **supplied-family verification** problem is PSPACE-complete. It is deliberately different from existential witness synthesis in a mixed family.

## 2. PSPACE upper bound

Boundary failures—undefined runs, Bad visits, nonfinal endpoints and diagonal/empty-suffix failures—are regular and can be detected in a polynomial product graph.

For a remaining bad member there is a proper flagged suffix agreement. The periodic bad-member normal form used by A017 writes a counterexample as

    x (u v)^e u,

with `v` nonempty. Work in the live product of `I` and `D`, with `K` reachable product states. The exponent can be shortened to at most `K`; in the terminal case the nonmerging argument gives the sharper original-state bound used by the implementation.

Fix the exponent, the source/target product states and the intermediate orbit chain. Existence of **one common** word `u` and **one common** word `v` realizing all repeated occurrences is reachability in a synchronous product whose tuple has at most `e+1` coordinates. A nondeterministic machine stores only the current tuple and a polynomial-space counter while guessing the path. The tuple has polynomial representation size because `e<=K`, and the outer choices can be enumerated in polynomial space. NPSPACE=PSPACE, equivalently Savitch's theorem also supplies a deterministic polynomial-space search.

The common-word condition is essential: choosing a different representative for each occurrence would be unsound in the recurrent-residual examples.

## 3. PSPACE lower bound with one forbidden pair

Reduce binary DFA intersection nonemptiness. Let `A_1,...,A_r` be the supplied DFAs. Build a terminal candidate automaton whose accepted macro words are exactly

    1 w_1 # 1 w_2 # ... 1 w_r #,

where `w_i in L(A_i)`. The leading `1` is a block tag that also makes empty data words harmless. Encode the macro alphabet by the fixed binary code

    0 -> 10,   1 -> 11,   # -> 00,

and enforce code alignment in the candidate automaton. Only code-boundary states are relevant to the flag.

Add **one** forbidden ordered pair: from the unique boundary entering block 1 to the unique boundary entering block 2. Those two states occur exactly once on every candidate.

Let

    B_i = 1 w_i #.

At those two positions the source remainder is

    B_1 B_2 ... B_r

and the target suffix is

    B_2 ... B_r.

The forbidden agreement holds iff the latter is a prefix of the former. Because `#` cannot occur inside a data word and every block starts with the same tag, equality up to the first delimiter forces `B_1=B_2`. After deleting that common first block from the comparison, the remaining prefix condition forces `B_2=B_3`; iterating through successive delimiter alignments forces

    B_1 = B_2 = ... = B_r.

Conversely, if all blocks are equal, then `B_2...B_r` is obviously a prefix of `B_1...B_r`. Therefore a bad member exists exactly when there is one word `w` accepted by every input DFA.

The construction is polynomial, binary, has one terminal accepting state, no Bad states, and a single forbidden pair. Thus **existence of a bad member** is PSPACE-hard from DFA-intersection nonemptiness. The verification question asks for absence of such a bad member, and PSPACE is closed under complement, so universal supplied-family verification is PSPACE-hard as well.

The classical source problem is the standard PSPACE-complete DFA intersection nonemptiness problem; the repository's word-synchronization notes record the primary-source attribution used for that fact. The new contribution here is the one-pair terminal reduction above, not the source complexity theorem.

## 4. Implementation and evidence

`experiments/regular_family_orbits.py` implements an exact shared-word orbit search. With both caps `None` it terminates. The explicit Python BFS can use exponential memory and is not claimed to be the polynomial-space implementation from the proof.

Every returned counterexample is checked by both the forward and reversed witness predicates. Caps return `UNKNOWN`.

The deterministic regression compares the orbit backend against the earlier exact backend on 43,069 cases, including 41,472 exhaustive two-state table/annotation instances. It independently rechecks all 23,781 returned counterexamples, includes 160 complete finite-family oracles, and exercises 100 finite instances of the lower-bound construction.

These finite checks support the implementations; the PSPACE theorem rests on the written all-input argument.

## 5. Frontier

This theorem classifies **verification of a supplied regular family**. It does not decide whether a mixed regular family contains some good member, and its bad-member bound is not a good-witness bound. The unrestricted frontier remains synthesis/normalization of the shared recurrent suffix obligations.
