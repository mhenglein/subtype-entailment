# Ten complementary agents for unrestricted Problem 1.7

Prepared 2026-09-06. These are proposed assignments, not launched agents.
No owner or active execution is implied. The coordinator should pin a common
immutable scientific checkout before dispatching workers.

## Scientific baseline and repository status

Use scientific checkpoint `fbce4a9825c60169db94f204c706436011345a5d` on
`research/run-profile-normalization` for the complete latest findings. This
includes the modular counterexamples, whole-word synchronization, delimited
convolution, target-frontier saturation, and full-profile run contraction.
The newer main navigation/collaboration checkpoint is
`46ebdcbf0d5c89ecf9405b86e0ad5115f9bcfd98`; preserve those human changes when
integrating the scientific branch. This campaign file does not itself merge
that branch or promote its written proofs to independently reviewed theorems.

Important: main's older Q002/Q003 OPEN labels predate the modular counterexample.
Their scientific-branch records mark both REFUTED, with independent review
pending. Do not use either conjecture as a premise. The broad Q001 skeleton
question is still open; polynomial-size skeletons cannot be assumed.

Read the exact problem, current scientific STATE, relevant notes and failed
attempts. Source checkpoints:
- [Scientific STATE](https://github.com/mhenglein/subtail/blob/fbce4a9825c60169db94f204c706436011345a5d/STATE.md).
- [Run profiles and remaining marker bound](https://github.com/mhenglein/subtail/blob/fbce4a9825c60169db94f204c706436011345a5d/research/RUN_PROFILES.md).
- [Target-frontier saturation](https://github.com/mhenglein/subtail/blob/fbce4a9825c60169db94f204c706436011345a5d/research/TARGET_FRONTIER.md).
- [Delimited convolution and negative-certificate obstruction](https://github.com/mhenglein/subtail/blob/fbce4a9825c60169db94f204c706436011345a5d/research/DELIMITED.md).
- [Whole-word synchronization and representation lower bounds](https://github.com/mhenglein/subtail/blob/fbce4a9825c60169db94f204c706436011345a5d/research/WORD_SYNC.md).

## The goal and what counts as finishing

The problem concerns arbitrary, possibly infinite trees over bottom and one
covariant binary product. Do not substitute finite-tree semantics. A positive
resolution needs an effective algorithm that terminates on EVERY valid input,
with soundness, completeness, and the semantic reductions established. A
negative resolution needs an exact computable reduction from an established
undecidable problem into this signature. Another restricted solver, a large
witness, or PSPACE hardness alone is not either resolution.

## Agent 1 - Independent semantic and formal audit

**Target:** audit the terminal-to-subtype realization and decidability transfer,
then the new run-contraction theorem and marker-bound equivalence. State the
exact remaining executable theorem in an interface that another agent can fill.

**First task:** read declarations and implementations back into mathematics.
Check quantifiers, satisfiability guards, normalization, arbitrary-tree semantics,
and termination claims. Prioritize an actual gap over producing another
conditional theorem. Audit the five-state negative example as a shared benchmark.

**Deliverable:** a reviewed dependency table and terminal-decider-to-original-
problem contract; either a precise flaw with a correction or a high-risk Lean
lemma independently checked against its intended statement.

**Do not:** insert an assumed global bound into a theorem and call that a solver.
Compilation alone does not prove that the formal statement matches the problem.

## Agent 2 - Saturation with recurrent targets

**Target:** extend the existing consistent-reference powerset construction to
flag targets that recur inside productive marker cycles.

**First task:** restrict initially to one recurrent target component. Define
exactly what a residual reference remembers about word contents and future
comparison guards. Find pairs of histories sharing a proposed summary but with
different valid continuations. Prove both simulation directions before merging.

**Deliverable:** an exact finite or otherwise terminating reference representation
with transitions, final test, completeness and termination; or a minimized
counterexample to the attempted quotient.

**Do not:** identify suffix words because their DFA states agree, or choose
incompatible reference tuples independently for different source observations.
Another special case is progress, not unrestricted coverage.

## Agent 3 - A marker bound from an obligation-aware algebra

**Target:** prove ANY computable existential bound M(k) on the number of
occurrences of the final symbol in a witness. The new numerical contraction
then turns it into an explicit general word-length bound.

**First task:** enrich transition effects with suffix obligations crossing block
boundaries. Prove a correct associative composition law. Investigate
factorization forests and idempotent-region replacement only after this law is
established. Preserve all new comparisons crossing a replacement boundary.

**Deliverable:** an effective algebra and normalization theorem yielding M(k),
or an exact obstruction to the proposed composition rule.

**Do not:** assume polynomial or elementary growth. Bounded factorization height
does not bound the number of children or justify pumping. Ordinary transition
monoids forget the critical border obligations.

## Agent 4 - Well-quasi-orders and antichain search

**Target:** replace a finite quotient with an effective well-quasi-ordered
symbolic search over exact residual obligations.

**First task:** specify configurations and the candidate order; establish
transition compatibility, the acceptance property, and effective finite
predecessor bases. Test the modular and counting families for infinite antichains
before claiming termination.

**Deliverable:** a terminating backward or coverability-style algorithm whose
target is proved equivalent to witness existence, or an explicit antichain or
monotonicity failure.

**Do not:** assume a well-quasi-order alone gives an algorithm. A lossy or
subsequence abstraction may destroy equality; coverability is not automatically
exact reachability.

## Agent 5 - Constrained tree automata

**Target:** encode the witness and its compared occurrences into a specifically
identified decidable class of tree automata with equality/disequality constraints.

**First task:** build a suffix/factor occurrence tree with explicit consistency
to ONE common word. Handle prefix relations, overlaps, state colors, empty
suffixes, and full borders. Check every hypothesis of the exact emptiness
theorem being invoked.

**Deliverable:** an effective translation and two-way model correspondence into
a proven decidable class, or the precise missing definability or closure property.

**Do not:** replace prefix equality by whole-subtree equality without proof.
Locally valid fragments may not belong to one realizable word. Arbitrary
constrained tree automata must not be treated as decidable.

## Agent 6 - Word equations and recompression

**Target:** obtain a finite regular-constrained word-equation representation
covering every internal suffix comparison, rather than a chosen finite sample.

**First task:** write the quantifiers explicitly: there exists a candidate word;
for every flagged pair of cuts there exists a mismatch. Seek a proved finite
mismatch cover and track state colors and crossing comparisons through pair/block
compression. Test the known delimiter-insertion counterexample.

**Deliverable:** an equisatisfiable finite translation to a theorem-supported
decidable fragment with an effective size bound, or a counterexample to the
proposed quantifier elimination.

**Do not:** invoke an existential word-equation solver for arbitrary quantified
equations. Do not add unrestricted length constraints or bound the number of
comparisons without a separate theorem.

## Agent 7 - Complete finite negative certificates

**Target:** construct effectively checkable refutations complete for NO instances.
If completeness is proved, enumerate them alongside the existing positive
witness search to obtain a terminating decision.

**First task:** derive the five-state negative example whose every finite
necessary-budget language is nonempty, without using necessary-emptiness as
its certificate. Develop rules for regular partitions, equal-tail obligations,
periodic inequalities, and cyclic derivations with a sound progress condition.

**Deliverable:** a finite certificate format, an independent verifier, an actual
proof object for that example, and a completeness proof or a separating instance
showing what rules are still missing.

**Do not:** confuse soundness with completeness. Dovetailing two searches does
not prove termination unless the required positive and negative coverage holds.

## Agent 8 - Direct prefix-closed tree semantics

**Target:** bypass the BorderAvoid route and decide the original constraints
through a model-equivalent logic, alternating automaton, or fixed-point system.

**First task:** translate all four normalized constraint forms into product-node
membership. Audit left/right concatenation, ancestor closure, forced roots,
denials, and separation. Prove definability of every cross-path relation before
using a tree-logic decision theorem.

**Deliverable:** a direct effective translation with both semantic directions
and a terminating target procedure, or the exact obstruction to the attempted
logical encoding.

**Do not:** replace regular infinite countermodels by finite trees, overlook the
semantic greatest full tree merely because top is not a constructor, or assume
that arbitrary cross-path relations are monadic-second-order definable.

## Agent 9 - Exact undecidability reduction

**Target:** test whether the exact terminal model can encode an undecidable
synchronization problem rather than only DFA intersection.

**First task:** starting from the whole-word synchronization construction, require
equality of two morphic images of the SAME nonempty tile sequence, as in a
Post correspondence reduction. Separate common indices, legal tile order, and
asynchronous output lengths. State the gap in each gadget before coding it.

**Deliverable:** a computable reduction with both directions, binary terminality,
and the subtype transfer audited; alternatively, a formal expressiveness
obstruction for the proposed gadget family.

**Do not:** substitute two independently chosen regular words for a shared tile
sequence. PSPACE hardness and huge witnesses are not undecidability. Delimiters
cannot be inserted without preserving every relevant agreement.

## Agent 10 - Adversarial abstraction synthesis

**Target:** discover composition-closed, existence-preserving residual summaries
through counterexample-guided synthesis and exact small-instance oracles.

**First task:** use independent forward and reversed predicates. Search actively
for histories with identical proposed summaries but incompatible continuations;
minimize each collision and send it to the relevant proof agent. Seed all
recorded counterexamples before running random searches.

**Deliverable:** an executable candidate abstraction with explicit semantic and
termination proof obligations, or a minimized obstruction family. A surviving
finite test set must still be followed by a mathematical proof.

**Do not:** assume the entire witness language must have a finite recognizer;
nonregular examples already exclude that in general. The goal may instead be
an existence-preserving normalization. Capped tests remain UNKNOWN.

## Shared execution contract

Pin one BASE SHA for all workers. Give each a separate worktree and a disjoint
seat directory for notes, experiments and result files. The coordinator owns
shared code, ledgers, STATE, registry and toolchain changes. Do not share an
active Lake build. Follow the current main AGENTS.md at integration: checked,
authorized updates directly to main; create a PR only when requested.

Do not mark any seat active before a worker actually starts. Record the exact
base, target, assumptions, seed, resource bounds, evidence and handoff. A suggested
initial finite-graph cap is 100,000 states; reaching any cap is UNKNOWN, never
NO. A finite word-length cutoff is not an unrestricted negative certificate.

The first handoff should contain one exact definition and one discriminating
lemma or counterexample, not just a survey. Every claimed final algorithm needs
its representation, transitions, semantic invariant, final test and termination
argument. Every reduction needs both directions and a size/encoding audit.

## Cross-review and priorities

Pair agents 2 and 9, 3 and 4, 5 and 6, 7 and 8, and 1 and 10. Agent 1 also
independently audits any proposed closing theorem. Agents may explore with
unreviewed dependencies explicitly labeled; no dependent theorem is promoted
until its dependency chain survives review.

Agents 2 and 3 are the most direct continuations of the present frontier.
Agents 5, 6 and 8 provide genuinely different formalisms. Agent 7 may close
decidability through complete refutations without a tidy witness bound. Agent 9
prevents assuming the answer must be decidability. Agents 1 and 10 reduce the
risk of ten workers amplifying the same mistaken premise. These are prioritization
judgments, not probabilities of success.

## Primary literature starting points

Applicability remains a proof obligation, not a black-box shortcut:
- [Factorization forests](https://arxiv.org/abs/0710.5130).
- [Well-structured transition systems](https://doi.org/10.1016/S0304-3975(00)00102-X).
- [Tree automata with local/global constraints](https://arxiv.org/abs/1302.6960).
- [Rationally constrained word equations and recompression](https://arxiv.org/abs/1405.5133).
- [Quantified word-equation limitations](https://arxiv.org/abs/1306.6054).
