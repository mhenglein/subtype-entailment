# Complete four-state terminal census

Date: 2026-09-05. A008, C034, E024.

**Status: exhaustive finite-case computational evidence plus a written
normalization proof.** Graph emptiness relies on the audited Python Sandwich
construction. This is not a Lean-checked theorem or a proof for larger state
counts. Unlike a word-length-only search, every negative case has a complete
finite necessary-automaton emptiness certificate.

## 1. Normalization covers every binary terminal-final instance of at most four states

Fix a candidate terminal accepting state f. Empty-word acceptance is handled
separately. For a nonempty witness, the start s and f differ.

Remove Bad vertices, diagonal-flagged vertices, and every p with G(p,f).
These are exactly forbidden by the boundary conditions of a witness ending
at f. Other terminal accepting vertices cannot occur before reaching f and
can be removed too. Any instance rendered empty by this removal has no witness
in the chosen final-state slice.

**Prefix-removal lemma.** If a witness w returns to its initial state after
reading a nonempty prefix u, the remaining suffix v is a witness from the
same initial state. Its run and all its suffix comparisons are restrictions
of the original ones. The same implication holds for Necessary(L,D) and
Sufficient(L,D): border lengths and induced periods of surviving comparisons
are unchanged, and the strong repeated-prefix test only loses occurrences.
Thus deleting transitions into the initial state does not change existence
of a witness or of a successful sufficient budget. This is NOT deletion of an
arbitrary interior loop; it discards the entire prefix through a start return.

Relabel the start as 0 and f as 3, pad unused states if necessary, and label
any remaining two states 1 and 2. Transitions into 0 can now be undefined.
State 3 has no outgoing edges. The six entries for states 0,1,2 each range
independently over {-1,1,2,3}: there are 4^6 transition tables.

Flags into the initial state cannot occur in strict position order, flags
from the terminal final cannot occur strictly, and diagonal/final-column
flags were already absorbed into safety. The only relevant pairs are

    (0,1), (0,2), (1,2), (2,1).

There are 2^4=16 such flag choices, hence exactly 65,536 normalized instances.
Every surviving word has identical annotations under the normalization.

## 2. Exhaustive graph certificates

For each normalized instance, the program first tries the zero-budget
necessary graph. Exact emptiness settles a negative case immediately.
Otherwise it searches all sufficient budget splits L+D<=2. Every positive
word is checked by both independent direct predicates and the sufficient
predicate. If no such word is found, it exhausts Necessary(2,2).
All searches have explicit state caps; reaching one would leave the case
unresolved, not turn it into NO.

The recorded complete run has:

- 65,536 normalized instances;
- 45,430 positive and 20,106 negative cases;
- 135,530 finite graph searches;
- zero unresolved cases or cap exits;
- largest returned witness length four;
- first successful budgets: 42,016 at zero, 3,398 at one, and 16 at two.

Together with normalization, these computations establish the all-length
classification for the stated finite-state class, conditional on the audited
finite-graph implementation. The classification gives a 31-word direct
existence decision (all binary words through length four), now justified by
the exhaustive graph proof rather than by assuming that a bounded scan suffices.
The helper `four_state_terminal_decision` is guarded to reject larger or
nonterminal-final instances as UNKNOWN.

Both bounds are sharp. The path language consisting only of 000 has four
states and exact budget two. The terminal instance with transitions
0--1-->1--1-->2, 2--0-->2, 2--1-->3 and G={(0,1)} has shortest witness 1101,
length four; its no-loop word 111 is not a witness.

## 3. Limits and reproduction

Run `python3 experiments/check_four_state_terminal.py` from the repository
root. Its loops enumerate the whole fixed finite space, without a time limit.
The saved result is [four-state-terminal.json](../results/four-state-terminal.json).
The broader candidate B<=k-2 for arbitrary terminal automata is NOT established.
The old 2k-4 family has nonterminal accepting states and does not settle this
terminal-only candidate. No new universal budget conjecture is promoted to a
claim by these checks.
