# Semantic transfer contracts for the formalization handoff

Date: 2026-09-18. Issue #23; support coordination #24; A010/A011/A018.
Actor: `semantic-bridge-review-20260918` (ChatGPT support/review).
Reviewed base: `35bff158f4620224f2608ba7bccf5ab770811853`.
Integration parent: `6b75aeb72099352b2328293384b00b9ca76e0cba`; its tracker-only
changes are preserved. The concurrent stage-6 formalization is tracked in #31
under #34; this report is support for it, not a claim on its Lean modules.

**Ordinary interface audit plus independently complete restricted-input tests.
Not a new unrestricted decision theorem, Lean formalization, human referee
report, or promotion of the candidate's status.** The formalizer's files and
shared definitions are unchanged. No new C/E/Q identifier is allocated.

## 1. Avoiding duplicate work

The issue's original semantic-review handoff is partly stale. The repository
already contains [the September 17 semantic reconstruction and audit](2026-09-17-semantic-bridge-independent-review.md),
its [independent checker](../experiments/check_semantic_bridge_review.py), and
its dedicated CI workflow. That review supports the conditional implication
from a correct total terminal BorderAvoid decider to normalized arbitrary-tree
subtype entailment. Re-running the same proof as a purported new contribution
would not be useful.

This addition makes the contracts needed at the eventual formalized algorithm's
boundary explicit, and checks their composition against literal model truth
rather than only another word predicate. It does not redo the graph-surgery or
preimage compiler formalization. The central ordinary closure proof and prior
semantic review retain their own evidence levels.

The original `papers/sep-topfree.pdf` blob is
`f5ff7db92590612a8d522fbdcd05257752ea082d`. Its binary contents could not be
retrieved in this session: connector metadata worked, but binary download and
runtime Git access did not. This is therefore NOT a fresh page-by-page reread
of the memo. It reads the repository's exact semantic reconstruction, the prior
[Sections 1--6 audit](proof-audit.md), C029/C031 notes and the pinned executable
bridge. Fidelity of those records to the source memo remains an explicit
inherited dependency, not an independently re-established fact here.

## 2. The final statement must retain arbitrary valuations

Let `Word = List Bool`, and represent a tree by a prefix-closed subset of Word.
The semantic valuation type must range over ALL such subsets. It must not
require decidable membership, a finite set, or a finite automaton presentation.
Specification-level classical reasoning is distinct from a runtime oracle.

For X prefix closed, its tree domain is

    {epsilon} union X union {wa : w in X, a in {0,1}}.

Label X by product and the remaining domain addresses by bottom. In particular
X empty still gives a bottom ROOT. The product-address operation is

    Prod(X,Y) = {epsilon} union 0X union 1Y.

Subtyping is inclusion. An infinite full tree is a semantic greatest element;
this does not add a top constructor to the input language.

Write `Models(C,rho)` for the four normalized clauses and

    Sat(C) := exists rho, Models(C,rho),
    Entails(C,alpha,beta) := forall rho,
        Models(C,rho) -> rho(alpha) subseteq rho(beta).

The final executable Boolean should be equivalent to Entails on every valid
finite input, including UNSAT inputs. Existence of an arbitrary classical
`Decidable` value is not an executable algorithm.

Naming a finite compound expression requires BOTH product inequalities. A
bottom name is constrained below bottom. Extension/restriction of valuations
must be proved for the naming construction, including fresh query names.
`denial_bridge.normalize` consumes ALREADY normalized tuples; its name must
not be mistaken for an implemented parser/normalizer for arbitrary surface
expressions. The current tests begin at the normalized boundary.

## 3. Exact dependency contracts, without changing the current Lean interface

These are mathematical specifications for coordination, NOT new compiled Lean
declarations or a request to edit the formalizer's files immediately.

| Contract | Required statement | Existing support | Still needed for end-to-end Lean |
|---|---|---|---|
| Valuation representation | arbitrary trees correspond to all prefix-closed product-address sets; products/order agree | prior semantic review Section 2, original audit | representation theorem and input normalization |
| Executable satisfiability | `satCheck(C)=true iff Sat(C)` | finite forced-root closure and denial reachability; `build` | verified finite saturation/search, not a classical branch on Sat |
| Separating-path bridge | under Sat(C), `not Entails(C,a,b) iff exists w, Witness(I_C,w)` | prior review Sections 3--5; three-summary construction | exact seed, reachability and ordered-cut correspondence |
| Structural absorption | every defined successor of any final is final with EMPTY incoming flag column | prior review Section 6; actual reversed-summary alphabet sources lie in BF | derive from constructed summaries, not assume for arbitrary annotated inputs |
| Infinite branch | under absorption, `infCheck(I)=true iff exists witness whose endpoint reaches a safe cycle` | C029, prior review Section 7; native periodic monitors | total finite algorithm and its scoped correctness theorem |
| Terminal restriction | `Witness(I) inhabited iff InfWitness(I) or Witness(J(I)) inhabited` | C031, prior review Section 8 | safe-edge restriction, endpoint extension, same-run witness transfer |
| Terminal decision | total executable `terminalCheck(J)` iff a terminal witness exists | proposed rank-query proof/compiler; current Lean structural dependencies only | central graph/query closure, termination, correctness and effective bound |
| Composition | UNSAT entails; otherwise negate the disjunction of the two existence answers | proof below, executable boundary tests | instantiate the preceding proved interfaces without hidden hypotheses |

C030 maps terminal instances INTO subtype systems. It is useful for reverse
expressiveness and regression models, but is NOT needed for the sufficient
subtype-to-terminal route. Proving C030 alone cannot discharge C031's direction.

The current `TerminalRank.lean`/`RankMilestones.lean` rank and first-return
results do not certify any of the semantic rows or silently instantiate
`Conditional.lean`'s budget hypotheses. The intended continuation remains the
formalizer's coloured graph and shared-query work.

## 4. Seed closure and satisfiability cannot be interchanged

For a proposed separating path w, let

    Seeds_w = {(f,epsilon): f in BF}
              union {(alpha,u): u prefix-of w}.

The least propagation closure M_w must include BOTH seed families. A model
containing (alpha,w) contains every prefix seed and every forced root, so it
contains M_w. The prior review proves M_w is prefix closed because every push
target is in BF. The left end of the stack is consumed by a pop; prefix closure
of tree addresses removes letters from the RIGHT. These two operations should
not be conflated in a formal definition.

Satisfiability first certifies that the forced-root closure avoids denials.
Seed safety for alpha alone does not discharge that separate branch. This is
the explicit premise omitted from one paragraph of the original memo as noted
in the earlier audit, and supplied in the reconstructed proof.

The test retains `x x b <= x, b <= bottom`, whose regular least model has
X(x)=0*, X(b)=empty. It refutes x<=b and has no finite tree model. The language
0* is checked by complete automata-product equivalence, not long finite words.
No finite-model enumeration is claimed to cover this example.

## 5. The exact absorption requirement and terminal restriction

For an annotated automaton I define

    Safe = Q minus Bad minus {q : G(q,q)},
    Z = {q in Final : forall p, not G(p,q)}.

The relevant absorption contract is

    f in Final and delta(f,a)=q  implies q in Z.                 (A)

It is stronger than closure of Final under transitions. In actual summary
instances, the reversed pop summary's letter edges start only at forced-root
controls. A final subset avoids all such controls, so after the next letter
that subset is EMPTY. This proves (A) for the constructed inputs.

Construct J on the SAME original state labels. Remove every edge with an
unsafe source or target. Its finals are exactly the ORIGINAL final states
that are safe and have no outgoing edge AFTER this pruning. Retain the original
start, Bad set and ORDERED flags. No sink is newly declared accepting merely
because it is a sink.

Under (A), safe extensions of witnesses preserve acceptance and all comparisons.
Given any witness w, either its endpoint reaches a safe cycle, or its reachable
safe subgraph is acyclic. In the latter case extending w to a safe sink takes
at most k-1 edges and produces a witness of J. Conversely every J witness has
the same accepted safe run and comparisons in I. Thus

    HasWitness(I) iff InfWitness(I) or HasWitness(J).             (B)

Here `InfWitness` may be defined by reachability of a cycle in a FINITE safe
graph instead of quantifying computationally over infinite streams.

### Small guards against accidental weakening

**Final closure is insufficient.** Let states 0,1 both be final, start 0,
0 --0--> 1, and no other edges. Let G={(0,1)} and Bad empty. Epsilon is an
original witness; `0` is not. J only accepts `0`, which is bad. There is no
infinite continuation. Thus (B) fails if (A) is replaced by final closure.
The example violates (A); it is not a counterexample to the existing bridge.

**Prune before choosing sinks.** Start 0 is final, its only edge goes to Bad
state 1. Epsilon is a witness and 0 becomes a safe sink after pruning. Selecting
only the raw graph's terminal finals would lose it.

**Do not promote nonfinal sinks.** With two disconnected terminal states, start
0 nonfinal and only 1 final, there is no witness. Making every sink final would
incorrectly make epsilon a witness.

**Do not erase initial unsafety.** A removed initial state cannot be treated as
an ordinary new safe root; the empty word is still rejected.

## 6. Composing total algorithms and composing capped evidence are different

Assuming the exact total interfaces above, the final mathematical program is

    if not satCheck(C): return true
    I := summarize(C,alpha,beta)
    return not (infCheck(I) or terminalCheck(J(I))).              (C)

UNSAT gives vacuous entailment. On SAT inputs the bridge and (B) show that the
disjunction is exactly non-entailment. Totality comes from the explicit total
subroutines. This is a proved logical composition conditional on those stated
interfaces, not a proof that all their Lean implementations now exist.

The executable audit uses three-valued evidence instead. It makes the following
rules explicit:

| SAT status | Infinite branch | Terminal branch | Permitted conclusion |
|---|---|---|---|
| UNSAT | not called | not called | ENTAILED |
| UNKNOWN | any/unavailable | any/unavailable | UNKNOWN |
| SAT | verified YES | any | NOT_ENTAILED |
| SAT | any | verified YES | NOT_ENTAILED |
| SAT | certified NO_INFINITE_EXTENSION | certified NO | ENTAILED |
| SAT | NO_INFINITE_EXTENSION | UNKNOWN | UNKNOWN |
| SAT | UNKNOWN | NO | UNKNOWN |

A bare YES label is trusted only according to its subroutine contract; returned
words are independently checked. The code's terminal oracle is complete only
on a CHECKED acyclic safe graph and returns UNKNOWN outside it. Consequently
this audit wrapper is NOT an implementation of the unrestricted proposed
terminal algorithm. It never converts a guessed word cutoff or a failed
certificate into terminal NO.

### Concrete capacity bounds for the older native components

For n normalized variables, `denial_bridge.build` records subsets of n, n and
n+1 NFA nodes. Therefore it has at most 2^(3n+1) summary classes. Passing this
integer as `max_classes` avoids a DEFAULT-cap UNKNOWN in the mathematical
construction. This does not bound the length of a separating word.

In C029, a fixed primitive period of length d<=k has memory: a current state,
one phase modulo d, d subsets of k cut states, and one conflict bit. There are
at most 2*k*d*2^(k*d) such memories. Hence 2*k^2*2^(k^2) is sufficient for each
period-phase search. All preceding graph/branch/lasso enumerations are finite.
These elementary state-count bounds do not replace C029's semantic proof.
The existing functions expect integer capacities; passing None is not an
implementation of uncapped execution for these particular APIs.

Host memory failure is not a theorem counterexample or a negative certificate.
The test wrapper does not promise to catch every host exception, run a parser,
or efficiently materialize these large bounds on arbitrary huge inputs.

## 7. Independent complete semantic tests

[New checker](../experiments/check_semantic_bridge_audit.py),
[deterministic result](../results/semantic-bridge-audit.json).

A deliberately independent oracle starts with acyclic upper-product constraints:
variable n-1 is denied, and each variable p<n-1 has an upper product whose two
children have larger indices. Let h(n-1)=0 and
h(p)=1+max(h(left),h(right)). Descending induction proves EVERY satisfying
arbitrary-tree valuation gives p a tree of height at most h(p). Extra lower,
variable-inclusion and denial constraints cannot enlarge these bounds.

Thus all finite prefix-closed sets at those heights enumerate ALL models of
these inputs, including the case of no model. This is not an assumption that
arbitrary inputs admit bounded trees. Evaluating each normalized inequality
uses literal set inclusion and Prod, not saturation or the summary automaton.
For each query the resulting universal model truth table is compared to (C),
using unchanged native bridge/C029 and the checked-DAG terminal oracle.

The executed corpus has 200 such systems (119 satisfiable, 81 unsatisfiable),
12,804 valuations examined, 723 satisfying valuations, and 2,500 complete
queries: 1,932 entailed and 568 not entailed. Every returned separating address
is checked against the independent complete valuation set. Thirty-two also
receive exact regular canonical-model checks at all depths.

A second complete all-tree oracle uses inputs with NO lower-product constraints.
All-bottom is a model. The query is entailed exactly when beta is in alpha's
variable-inclusion epsilon closure or that closure reaches a denied variable.
Otherwise put only the root in every variable in that closure, with all others
bottom; every upper product permits a root, so this is a countermodel. All
2,304 selected two-variable query combinations agree with the composed code.

There are also 27 status combinations, a forced-root UNSAT short circuit, an
intentional summary-cap UNKNOWN, the boundary fixtures above and the exact
infinite-spine language check. Across 4,804 complete query oracles there are no
unintended UNKNOWN results or mismatches. These finite corpora do not prove the
unrestricted bridge; they independently check its executable interfaces.

An initial test incorrectly demanded that C029 return epsilon on the infinite
spine fixture. It returned the equally valid word `0`; C029 does not promise a
shortest witness. The TEST expectation was corrected and epsilon's canonical
model checked separately. No reviewed source or mathematical theorem was changed.

Four dependency blobs are enforced by the checker and recorded in the result.
An archive copy was used only after matching those hashes to the pinned remote
files. The existing `check_infinite_extensions.py`,
`check_unrestricted_continuation.py` and `run_experiments.py` were also replayed;
their three saved outputs remained byte-for-byte unchanged from the archived
baseline. This is targeted replay, not the full repository suite or new Lean CI.

## 8. Handoff and limits

Recommended next formalization support action: agree these interface contracts
with the proof owner, then formalize the semantic transfer in separate modules
when the appropriate shared types are fixed. Do not start competing definitions
of `Instance`, words, entailment or query graphs. The current graph-surgery and
preimage work stays with its author. Reuse #23 for the semantic track.

No substantive semantic flaw was found in the reviewed reconstruction. The new
value is the explicit dependency boundary, capped-result discipline and complete
restricted semantic oracles. The original PDF reread was unavailable; arbitrary
surface-input normalization and every semantic theorem are not newly formalized.
Existing review status and the proposed unrestricted result remain unchanged.

Reproduce from the repository root, Python standard library:

    python3 experiments/check_semantic_bridge_audit.py --output /tmp/semantic-bridge-audit.json
    cmp results/semantic-bridge-audit.json /tmp/semantic-bridge-audit.json

Issue comments hold scope, publication and handoff status. No assumption of
background work, new agent assignment or a human independent review is made.
