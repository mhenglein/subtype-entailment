# Issue 67 independent fixture investigation

Session: issue67-independent-fixtures-20260920. Input revision:
`19b06d4fed9da635d9b911f0e908d04e4fc4b099`.
Scope approved explicitly by publication-sequence-20260920 in #67 comment
5750364458, after request 5750338067 and #37 request 5750340234.
Only the four new paths/directories in that agreement are owned. No existing
compiler, Lean interface, CI, ledger or main branch is changed.

## Route recorded before the test implementation

1. Read the original Witness definition, including i=j and empty suffixes.
   Implement direct string/cut checking without calling the production predicate.
2. Verify an acyclic transition graph and derive a complete bound on forward
   and reverse paths before enumerating references. A resource limit is not
   such a bound.
3. Use the four-state unary path accepting only 000. The safe references
   0, 00, 000 have labels (3,2), (3,2,1), (3,2,1,0). Finishing without a return
   fails at the first two and succeeds by empty completion at the last.
   The two first returns are actual overlapping/singleton-return steps.
4. Distinguish an executed, certificate-directed pair of compiler invocations
   from an automatic whole-terminal decision. Only an observed winning query
   with provenance depth two establishes the latter.
5. For a complete nontrivial two-atom union, use root-to-end observers whose
   only edges are S, and specialize the existing syntactic compiler to its
   satisfiable shape classes. The proof of this specialization must account
   for every omitted shape; a certificate subset is insufficient.
6. Use the acyclic five-state graph with edges 0-0->1, 1-0/1->2, 2-1->3,
   3-0->4 and accepting state 4. Base (0,(4,3)) has exactly two first returns:
   (010,(4,3,2,1)) and (0110,(4,3,2,1,0)). Exact S-length 3 together with odd
   S-length is positive. Exact S-length 4 together with odd S-length is
   negative although each conjunct separately is positive. These observations
   must use one common extension, not separately chosen extensions.
7. Keep strict completed checks separate from capped original-enumerator and
   whole-decision diagnostics. Record hashes, limits, resource use and provenance.

No test agreement substitutes for the repository's all-input proof. Full Lean
execution is NOT RUN in this container, which has neither Lean nor Lake.
The local worktree starts at a clearly labelled partial connector-source
snapshot, not at a claimed full clone of the original commit.

## Independent semantics and completeness of the small oracle

For a defined run q_0,...,q_n on w, the literal predicate checks finality at
q_n, no Bad state at ANY cut, and for all 0 <= i <= j <= n rejects exactly
when (q_i,q_j) is flagged and w[j:] is a prefix of w[i:]. This includes i=j,
the initial cut and j=n. It is a separate implementation, not a call to
border_lab.witness, border_witness, a KMP border chain, or the compiler oracle.

The reverse-reference predicate separately checks every transition and every
literal border of every prefix. Original table-observer queries use an
independent product-graph BFS and exhaustive vertex assignments. Unlike the
older fixture helper, this evaluator does NOT delegate to Observer.allows,
Observer.move, production path, or production model. The data classes are
shared as storage only. Production model remains the evaluator under test.

Every instance in the strict family is acyclic. A DFS checks acyclicity over
ALL states, including states unreachable from the original initial state,
and computes the maximum forward path length. Reversing a reverse-labelled
run gives a forward path, so this bounds all reverse references too. The
oracle enumerates every defined forward path and every safe reverse
continuation from the specified base. Safety is hereditary under prefix,
so pruning an unsafe reverse prefix cannot discard a safe extension. The
first-return condition requires exactly one nonzero occurrence of B in C,
ending at C's last position; overlapping occurrences are not discarded.
Thus failure after exhaustion is genuinely NO within these fixtures, not
failure below a guessed word-length cap. The oracle refuses cyclic inputs.

## Two promotions, without overstating automatic coverage

The positive unary instance has only the accepting run
0 -0-> 1 -0-> 2 -0-> 3, with state 3 terminal. Its only accepted word is 000.
All flags and Bad states are empty. The sole safe one-letter base is
B1=(0,(3,2)). Its only first return is B2=(00,(3,2,1)); the latter's only first
return is B3=(000,(3,2,1,0)). A no-return finish at B1 or B2 cannot take the
next 0, because that letter already completes a return. Neither endpoint
label is the initial state. B3 finishes with no new letters. Thus zero and
one promotion cannot work, whereas two do. The second return has occurrences
of 00 at offsets 0 and 1: they overlap. Each new strip has one vertex, so
FIRST, LAST and the query's fresh endpoint have coincident physical positions
but different roles.

The original compile_diagram is invoked backwards twice from the original
finish query. The resulting base formula is checked; reconstruction replays
both stages on the SAME intermediate reference. The original forward
Witness predicate then checks the final word. Profile receipts report one
successful compiler return at depth 1 and one at depth 2. They do not infer
depth from k-2 or from witness length. The original finish-query and graph
finishing implementations both match the independent no-return predicate.

This is **certificate-directed two-promotion compiler replay**, not a claim
that the automatic decision enumerator found its winning depth-two formula.
The latter was actually run separately and remains UNKNOWN at the cap.
The unary fixed-word instance itself is an old baseline, not a new theorem.

The flag (0,1) invalidates the only accepted word because suffix 00 is a
prefix of 000. Reversing this ordered flag to (1,0) leaves the word valid:
the flagged target precedes its source and is never an eligible later cut.
The flag (1,1) tests a diagonal. The flag (0,3) tests the empty suffix, even
though the initial and final states differ. One-state terminal instances
cover the empty witness, diagonal denial and Bad denial. Their automatic
frontend exits are recorded as boundary coverage, not promotions.

## Complete two-atom compiler-union regression

The five-state instance is

    delta = ((1,-1), (2,2), (-1,3), (4,-1), (-1,-1))
    initial = 0; final = {4}; Bad = {}; flags = {}
    B = (word 0, labels (4,3)).

The all-state path bound is four. Its complete first-return set is
C3=(010,(4,3,2,1)) and C4=(0110,(4,3,2,1,0)). The continuation 0100 is not
another first return: it has already returned at 010. Note that a safe
reference need not end at the original initial state.

Both query variables are shared: r is the root, e is the distinguished end.
A_d is the table observer accepting exactly d S edges. O is the two-state
parity observer accepting an odd number of S edges. The positive query is
A_3(r,e) AND O(r,e); its unique successful reference is C3. The negative
query is A_4(r,e) AND O(r,e). Each negative conjunct separately succeeds
(A_4 on C4, O on C3), but their conjunction cannot. On a prefix graph the
S-path from root to end has exactly the reference length. This gives a
written expected-answer proof independent of the compiler and kills the
incorrect split-generator mutant AND_a EXISTS_C atom_a(C).

The positive compiled clause reconstructs C3. Original finish_on_graph then
adds 0 and yields the original witness 0010, checked independently. The
positive branch has TWO distinct fresh mark classes and one nonempty
interval observed simultaneously by BOTH observers. The negative regression
also executes the actual joint-interval move/path code, not just a unary
test or an inconsistent top-level equality.

### Why the S-only projection is a complete union, not a certificate sample

The following statement concerns ONLY the imported Python compiler, safe
nonempty bases, root/end queries with no equality/disequality, and table
observers with true colour predicates and only S transitions. It is an
ordinary proof for the test enumerator, not a new checked Lean theorem.

Let U be the disjunction emitted by the original iter_diagrams plus
compile_diagram, with rejected diagrams omitted. Let U_S be the disjunction
compiled from s_only_diagrams. For every such base B:

    model(P(B), U) exists iff model(P(B), U_S) exists.

Coverage of all omitted classes is as follows.

1. A root-tested variable cannot be fresh: every fresh colour has root=false.
   An end-tested variable cannot be core: the old endpoint is changed to
   end=false and every other old vertex already has end=false. Thus r is
   core and e fresh. The latter's mark is LAST, because only that mark has
   next_bit='', hence fresh end=true. Invalid alternative roles/orders have
   false unary tests, rather than undiscovered witnesses.
2. Every exit or wrap portal has label F, K0 or K1. Every K entrance likewise
   uses a K label. Table observers with only S edges cannot traverse any
   such portal, for ANY controls or colours. Their compiled portal tests or
   edge observers are unsatisfiable. Hence every surviving atom has exactly
   the compiler-offered core / enter-S / forward shape. There is no fresh
   backward excursion or hidden repeated entrance left to guess.
3. Its only fresh marks are FIRST, LAST and e=LAST. Up to the irrelevant order
   of names inside a coincident class, there are exactly two weak orders:
   FIRST=LAST=e, or FIRST < LAST=e. The projection enumerates both. Its
   nonempty forward span has no internal marked seam.
4. For each atom, enumerate every initial control, final control and S-edge
   (p,q) for the entrance. All other entrance seam pairs reject. These are
   exactly the remaining four seam controls. For each weak order enumerate
   all original states, both first bits, all permitted nonfinal next bits
   and every old-end forbidden mask, using the original enumerator's safe
   first-emission filters. Nothing depends on a sampled concrete extension.
5. Every resulting diagram is compiled by the UNCHANGED compile_diagram.
   The offered path shape is checked using the first element of the actual
   path_shapes generator. All finite role/order/control/state/colour choices
   occur in the original iterator; permutations of names within a class do
   not affect any clause. Therefore each surviving original clause is either
   represented with identical semantics in U_S or belongs to an explicitly
   unsatisfiable class. Conversely every U_S clause is an original offered
   clause up to that harmless renaming/order convention.

This proves both directions of the projection equality. The independent DAG
oracle establishes the expected existential answer. The harness then evaluates
EVERY compiled clause of U_S and reconstructs every returned positive model.
The finite scope is structural and explicit; no work/time cutoff defines it.
This is more than extracting a diagram from known positive examples, but it
is deliberately NOT reported as physically exhausting the unpruned iterator.
That iterator is retained separately as a capped diagnostic.

## Executed receipts

Strict acceptance: **13/13 PASS** on the pinned Python sources, repeated with
PYTHONHASHSEED 2026092067 and 77. Logical records, counts and coverage agree
exactly after excluding commands, hash seed and resource timings.

| Union | Candidate diagrams | Rejected | Compiled | Satisfied |
|---|---:|---:|---:|---:|
| exact 3 and odd | 5,280 | 400 | 4,880 | 1 |
| exact 4 and odd | 7,040 | 560 | 6,480 | 0 |

The actual two-observer interval move returned 58,512 times in the positive
run and 84,704 times in the negative run. These include rejected candidates;
they are not counts of accepted generators. The positive satisfied clause
has two distinct mark classes and a two-observer interval. The negative
query's 6,480 compiled clauses all fail despite individually positive atoms.

The coincident-wrap fixture uses a genuinely nonempty K0 self-wrap on the
fresh endpoint together with a zero-length atom at two equal query variables.
The negative companion requires the two unique end vertices to differ.
These are on a terminal acyclic input, unlike the older nonterminal toy.

Six capped diagnostics remain **UNKNOWN**: two calls of the original Python
whole-terminal decide and four original unpruned compiler unions. Each
stopped at 100,001 work units with a 100,000-unit limit. Both whole-decider
runs constructed 5,784 depth-one clauses and no observed depth-two winning
query. A zero-witness count in a raw union prefix is not a negative result.

A forced one-microsecond wall cap returns a child UNKNOWN and makes strict
acceptance exit 1. It is not relabelled PASS. Two larger shell orchestration
attempts were interrupted by the outer execution timeout; their incomplete
outputs were not used as successful evidence. The final strict/stress/replay
receipts above were rerun to completion with the final harness hash.

## Source pins, environment and commands

The five production files copied through the connector exactly match these
Git blob IDs; source_receipt verifies them before execution:

- border_lab.py: 1144ae52379e0417772e79582269cacd91c5bc17
- rank_query_prefix.py: 135d3cb960d07dfddefd74dd255bba289a08af1b
- rank_query_graphs.py: 6fcc612e47ef65edbb7ec9ff973a528a422da8e4
- rank_preimage_core.py: fe297ab4f2252468b1734f6885765cde0d2cecb9
- rank_preimage.py: 852fa7d7ba199b9d91ab24a8f7b5abf29ed8819b

Harness SHA-256: a065f6e7866ecb5dea2177fff516df981055093698f9f6fbaa9e7f6b10564097.
Fixture file SHA-256: 701e04ef556ee0b1fea87dbf9bc792389b89dddd7497c708926212deed84a1fe.
Every case's canonical JSON SHA-256 is in the receipt. No random search was
used; the two seeds control Python hashing only.

Local environment: Linux 6.18.44 x86_64, glibc 2.41, Python 3.13.5 / GCC 14.2.0,
five reported CPUs. Separate local source repository /mnt/data/issue67-source
and worktree /mnt/data/issue67-work; outputs /mnt/data/issue67-runs. The local
snapshot commit is explicitly NOT the original GitHub revision. Direct git
access failed DNS; Lean and Lake are absent. Only the five-file dependency
closure was materialized, not a full repository clone.

Strict limits per child: 60 seconds wall, 55 CPU seconds, 1024 MiB address space.
Stress limits: 20 seconds wall, 18 CPU seconds, 1024 MiB, 100,000 work units.
Each child is a fresh subprocess. Timings include diagnostic instrumentation;
they are NOT matched optimization benchmarks. Peak RSS is the process-lifetime
high-water mark, including startup, not incremental compiler allocation.
Strict child work totals 6.9361 seconds wall; parent-observed time, including
process startup, is 15.0650 seconds. Strict peak RSS ranges 95,656-96,172 KiB.
Exact user/system CPU, wall and peak memory per case are in receipts.

Run from a checkout whose five sources match the pins:

```sh
python3 experiments/issue67_independent_fixtures.py --output /tmp/issue67/strict.json
python3 experiments/issue67_independent_fixtures.py --seed 77 --output /tmp/issue67/replay.json
python3 experiments/issue67_independent_fixtures.py --mode stress --max-work 100000 --wall-seconds 20 --cpu-seconds 18 --output /tmp/issue67/stress.json
```

The actual local commands also passed `--snapshot-kind partial-connector` and
used the isolated output paths above. Strict UNKNOWN fails acceptance; stress
UNKNOWN is retained without treating it as a disagreement or proof of NO.

## Handoff and remaining gaps

This contribution does not close #67. The main unresolved coverage requirement
is an automatically discovered successful depth-two terminal decision through
the checked native Lean backend. The original unpruned unions also did not
finish at the recorded caps. Native Lean, full-repository checks, and original
finite-expression C081 frontend execution are **NOT RUN**. This is not an
end-to-end native subtype acceptance receipt.

The S-only projection has a complete ordinary scope proof above, but no
separate human/agent or Lean check of that new proof is claimed. Ask the
integrator/reviewer to challenge steps 2-5 and replay the harness from a full
checkout before adopting it in CI. No existing interfaces or proof statements
were changed, and no main push or merge is performed by this worker. The
integrator owns any later ledger/index changes and any expanded Lean scope.
