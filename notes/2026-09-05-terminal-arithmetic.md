# Exact arithmetic for fixed skeletons and flat terminal automata

Date: 2026-09-05. Approach A016, claim C033, experiment E023.

**Status: WRITTEN PROOF + IMPLEMENTATION + REPRO. Not Lean-checked.**
The memo already claims fixed-skeleton checkability in Proposition 7.5.
This work supplies an explicit translation, a guarded solver, and a complete
finite skeleton cover for flat terminal candidate graphs. It does not claim
literature novelty for Presburger decidability or the fixed-skeleton idea.

## 1. Input and quantified statement

Fix a well-formed finite annotated DFA and a finite sequence of blocks.
Each block is either a fixed literal or a fixed nonempty word raised to its
own nonnegative integer exponent. Thus the candidate language is

    s0 u1^n1 s1 ... ud^nd sd,   n1,...,nd >= 0.

The repeated words need NOT be loops at the state where they start. All
partial transitions, Bad states, final states, diagonal flags, and empty
suffix obligations remain part of the problem.

**Theorem.** The exponent vectors producing witnesses are definable by an
effectively constructible Presburger formula. Consequently their existence
is decidable for this fixed skeleton, with no exponent cutoff.

## 2. DFA states and letters as arithmetic functions

Complete undefined transitions using a fresh rejecting sink. For each fixed
word u, its action T_u on the k+1 states is a finite function. From each
starting state, the orbit under repeated T_u consists of a finite preperiod
followed by a cycle. Enumerate both. T_u^n(q) is then expressed using finite
case distinctions, equality to small constants, and a remainder modulo the
fixed orbit period. These are Presburger-definable operations.

Every block boundary is a linear expression in the exponents. Within a block
u^n beginning at offset o, a position x has copy index floor((x-o)/|u|) and
phase (x-o) mod |u|. Apply the appropriate T_u power and then the fixed
prefix of u to obtain the DFA state c(x). The letter at x is the corresponding
fixed phase letter. Boundary states compose in block order. When a repeated
word is a loop at a known state, the implementation uses the simpler constant
boundary state; the general orbit formula remains available.

There is no multiplication of two variables. All divisions and remainders
are by positive, fixed integers. Positions outside a block are excluded by
its interval guard; zero exponents give empty intervals. Position N, the
whole word length, receives the final boundary state rather than a letter.

## 3. The exact witness formula

Admissibility says c(N) is final and every c(x), 0<=x<=N, is defined and not
Bad. The flag predicate is the finite disjunction over (p,q) in G of
c(i)=p and c(j)=q. Add

    for all i,j with 0<=i<=j<=N:
      G(c(i),c(j)) implies
        exists h: 0<=h<N-j and letter(i+h) != letter(j+h).

This is exactly the negation of each forbidden suffix-prefix agreement.
If i=j, no mismatch exists, correctly excluding diagonal flags. If j=N,
the offset interval is empty, correctly excluding a flagged empty suffix.
All variables range over integers with the displayed nonnegative guards.
Together with the exponent constraints, this is a Presburger formula.

### An exact elimination of the mismatch-offset quantifier

The implementation additionally expands the offset existential. Suppose i+h
lies in block P=[oP,eP), with fixed period word u, and j+h lies in Q=[oQ,eQ),
with period word v. Their allowed offset interval is

    lo = max(0,oP-i,oQ-j),
    hi = min(N-j,eP-i,eQ-j),       lo <= h < hi.

Their letters depend only on h modulo M=lcm(|u|,|v|). For every residue
0<=t<M, evaluate those two periodic letters using i+t and j+t. The first
h>=lo in that residue is

    lo + ((t-lo) mod M).

A mismatch in this block pair exists iff some residue has different letters
and this first h is below hi. Disjoin over the finitely many block pairs and
residues. Empty blocks and disjoint intervals correctly contribute nothing.
This leaves only the outer position quantifiers. It does not introduce
variable multiplication or assume that a bounded offset scan is complete.

## 4. Complete flat terminal candidate graphs

Remove unsafe vertices (Bad and diagonal-flagged), then restrict to vertices
reachable from the start and able to reach a final state. Require every final
state to be terminal. A productive cyclic strongly connected component is
**flat** here when each vertex has exactly one internal LABELLED edge.
Two letters to the same internal successor count as two edges, not one.
Edges leaving the component are unrestricted.

Every such cyclic component is one directed cycle. A run enters at a state q,
makes n>=0 complete turns around its fixed cycle word u_q, takes a fixed
proper prefix of that cycle, and leaves on an exit edge. Its contribution is
therefore u_q^n t for fixed t. Acyclic singleton components contribute fixed
edges. The SCC condensation is acyclic, so each component is entered at most
once, and there are finitely many component paths, entry states, and exits.

Enumerating these choices yields a FINITE, COMPLETE union of fixed skeletons
for the safe accepted language. Apply Section 1 to every skeleton. A witness
in any skeleton is a witness of the original instance. If every skeleton is
empty, no witness exists. This decides the entire flat terminal class,
including multiple successive unbounded loops and cross-block comparisons.

This is stronger than the earlier acyclic pre-final frontier: the nine-variable
nonregular separating language from C032 has two unbounded loops and lies
in this class. It is not a claim that every terminal graph is flat, or that
restricting an arbitrary graph to flat edge subsets preserves a witness.

## 5. What the executable implementation guarantees

`Skeleton.script()` exports the exact arithmetic formula in SMT-LIB.
`Skeleton.solve()` invokes an optional Z3 shared library in a child process.
A positive model is expanded and checked with BOTH independent word predicates.
Excessively large expansions, solver errors, missing libraries, and timeouts
return UNKNOWN. A negative answer must be confirmed by two Z3 entry points
(the ordinary solver and the `qe2` tactic pipeline). This is a safeguard,
NOT an independent proof assistant or a certified arithmetic proof.

The first prototype used a different `qe` pipeline. On the fixed zero-loop
case of C028 it produced a SAT answer rejected by independent word validation;
the ordinary solver and `qe2` returned UNSAT. That pipeline is not used.
The regression remains in the tests. No general external-solver bug claim is
needed for the mathematical translation, and no bad answer was promoted to a
research result. Backend trust and the written proof are recorded separately.

Theoretical decidability uses a terminating Presburger decision procedure.
The practical resource-limited runner is deliberately three-valued: its
UNKNOWN verdict is not a negative mathematical result. `decide_flat_terminal`
returns NO only for a complete cover whose every member has an exact negative
answer; a nonflat SCC or an incomplete schema enumeration returns UNKNOWN.

## 6. Evidence

Run `python3 experiments/check_terminal_arithmetic.py` with a Z3 shared library
installed. The recorded environment used Z3 4.13.3.0. There is no OpenAI API,
remote model, or API key dependency.

The checks compare 164 fixed-exponent formulas with the direct and reversed
word predicates: 40 SAT, 124 UNSAT, zero UNKNOWN in that bounded test.
They also compare complete schema covers against all 8,188 binary words
through length ten for four automata, including a two-cycle instance and a
period-two state action. Unbounded solver queries include an infinite empty
skeleton, the earlier loop obstruction, and a two-counter witness with both
counts at least 25. The count 25 is a test constraint, not a solver cutoff.

A nonflat productive SCC is explicitly rejected as UNKNOWN. Other exploratory
unbounded queries reached time limits and were not interpreted as negatives.
These finite checks validate the implementation on their inputs; the proofs
above establish the unbounded mathematical statements.
