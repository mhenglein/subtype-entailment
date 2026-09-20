# Issue 68: regular countermodel producer

Date/session: 2026-09-20, `regular-producer-68-20260920`.
Inspected upstream: `19b06d4fed9da635d9b911f0e908d04e4fc4b099`.
Branch: `codex/regular-producer-68-20260920`.

Status: the complete original-input graph producer is Lean-checked at the
source checkpoints recorded below. This began as an ordinary constructive
outline; source inspection, kernel checking and execution remain distinct. This note does not promote C084, amend any
ledger, or close issue 68. Its first version precedes source implementation.
The local worktree is a sparse inspection workspace: its initial synthetic
commit contains one byte-verified upstream Python file, not the whole upstream
repository. GitHub publication uses the actual upstream parent and tree.

## Contract, representation, and scope

Let `Word = List Bool`, with false/true denoting left/right. A tree is an
arbitrary prefix-closed subset of Word; it need not be finite or regular.
Bottom is the empty set. Product is `{[]} union 0.X union 1.Y`. Subtyping is
inclusion. A valuation assigns such a tree to each of finitely many variables.
Expressions are finite terms consisting of variables, bottom and product;
premises are a finite list of pairs of expressions. `ExprEntails G s t`
quantifies over every valuation satisfying all pairs in G. Inconsistent G
therefore entails every query. The query is not added to G.

The desired total producer returns `none` exactly on entailed inputs, and
otherwise returns `(v, graph, roots, word)`. Here `graph` is exactly
`RegularTreeCertificate.Graph v`: each node is bottom or a pair of successor
indices in `Fin v`; `roots : Fin n -> Fin v`; and `word` is finite. The output
valuation is the graph unfolding at roots. Every returned valuation must
satisfy every ORIGINAL premise, contain word in the left expression and omit
it from the right expression. Directed cycles are allowed and can denote
infinite trees. This is not a finite-tree certificate theorem.

The model record is the semantic graph/root/word portion of C084's certificate.
The latter additionally has a finite expression-node map and Boolean simulation
relation. Their automatic decoration is addressed below, but a verifier's
soundness must not be substituted for the producer's completeness.

## End-to-end route

1. Use the existing exact finite-expression normalization; preserve expression
   meanings and original variable roots, including query-only subterms.
2. For each candidate word, seed every forced root and every prefix at the
   left query variable. Form the full, unbounded propagation closure.
3. Recognize this closure by a finite NFA, using exact balanced/pop summaries
   and fixed seed suffixes on the RIGHT of reverse-pop words.
4. Determinize over one finite subset carrier, then interpret accepting states
   as product nodes and rejecting states as bottom. Prove exact language
   equality at each relevant root, not merely bounded agreement.
5. Use the existing exact supplied-word separation test. Convert the successful
   canonical closure to a graph, and restrict its roots to original variables.
   Preserve the exact chosen word through both operations.
6. Enter fair word search only after the C081 Boolean has answered negative.
   Its correctness supplies a successful finite word, hence termination of
   the one-sided search. Positive and inconsistent inputs do not enter it.

No assumed global shortest-witness bound, finite-model property, fixed shape
library or supplied arbitrary countermodel occurs in this route.

## Ordinary proof

### 1. Normalization and least closure

Name the finite input forest's products and bottom, as in
`ExpressionNormalization.normalized`. Each product name has both inequalities
with the product of its children's names; the bottom name has a denial.
The two inequalities force equality by inclusion antisymmetry. Induction on
finite expression syntax identifies each supported name with the expression's
value. Every original model extends to a normalized model; restricting a
normalized model to original variables recovers an original model. The same
identification holds for BOTH query expressions at EVERY address.
`normalize_separating_iff` explicitly preserves the supplied word. Shared
subterm names versus occurrence slots changes representation, not this argument.

For normalized constraints C, the finite system W has epsilon edges for
variable inclusions, pops from an upper product's parent to its children, and
pushes from a lower product's children to its parent. Stack top is on the left.
A lower product additionally forces its parent's empty address; a denial forbids
all addresses at its variable. These root/denial conditions are not pushdown
edges and may not be dropped.

Fix a candidate w and let S contain all forced roots `(q,[])`, and every
`(alpha,w.take i)` for `0 <= i <= length w`. The inductive closure D is exactly
reachability from S in W (`derived_iff_reaches`). Every derivation belongs to
every model containing S, by induction on its last propagation rule.

D is prefix-closed. Removing a suffix from a seed stays in S. Pops use one
extra retained letter in the induction hypothesis. A nonempty prefix of a
pushed word follows the corresponding shorter push; its EMPTY prefix comes
from the forced parent root. This is precisely where forced roots are needed.
If D avoids all denied variables, its inclusions/pops/pushes and forced roots
satisfy all normalized premises. Conversely, any model containing S prevents
D from hitting a denial.

If an arbitrary model separates alpha/beta at w, it contains every seed in S.
Consequently D is included in that model, avoids denials, contains alpha at w,
and omits beta at w. Conversely these tests on D themselves give a model.
There is no separate satisfiability assumption: all forced roots are present,
so an inconsistent input cannot pass. This proves the exact supplied-word
criterion and existence of such a word on EVERY negative input.

### 2. Exact finite language construction: coverage

The balanced relation B on W is the least relation containing identity and
epsilon edges, closed under composition and matching push/B/pop wrapping.
Every generated pair has such a run; first-return decomposition of a balanced
run proves the converse. A monotone finite table reaches a fixed point after
at most the number of pairs has been added. This is not a stack-height bound.
The reversed system reverses all edges and swaps push with pop.

`Pop_W(p,x,r)` means consuming x through pops with balanced excursions before,
between and after them. Its empty-word case is B. Thus it is the language of
a finite epsilon NFA. Existing `reaches_iff_normal` gives

    Reaches_W((p,u),(q,v)) iff
      exists x,y,z,r,
        u = x ++ z and v = y ++ z and
        Pop_W(p,x,r) and Pop_reverseW(q,y,r).

For the ordinary decomposition, take a configuration of minimum stack height
on the finite run. Its stack is an untouched common suffix z: no earlier or
later operation can pop below that height. Before this minimum, successive
net pops remove the initial prefix x, with balanced excursions between them.
Read the remaining half backwards in the reversed system to obtain the
corresponding net-pop reading of y. The shared minimum control is r. In the
other direction, append z to the two pop computations and reverse the second;
concatenating at (r,z) reconstructs the original reachability. This argument
allows arbitrary balanced loops and does not assume bounded stack height.

Equivalently, choose a cut i in the finite seed u, consume `u.take i` in W,
and retain `u.drop i` on the right. Let

    Attachment(r,z) iff exists (p,u) in S, i <= length u,
      Pop_W(p,u.take i,r) and z = u.drop i.

All attachments are effectively enumerable. From control q, the exact
language is

    L(q) = { y ++ z | exists r,
      Pop_reverseW(q,y,r) and Attachment(r,z) }.

For coverage, factor an arbitrary finite propagation derivation by the normal
form. Its minimum-stack cut supplies an attachment. The reverse-pop part is
read from q, then its untouched suffix is read. No bound on derivation length,
stack height, repeated visits or cycles is imposed.

### 3. Reconstruction and an epsilon-free presentation

Use disjoint tagged states `control q` and `suffix z`, where z ranges over
suffixes of the finite seeds. A suffix state reads exactly its remaining word
and cannot return to a control. Only empty suffixes accept. Sharing identical
suffixes cannot switch to another unfinished control computation.

The ordinary Python extractor uses reverse-balanced epsilon edges and attachment
epsilon edges. The formalization plan uses the equivalent epsilon-free form:

- `control q --a--> control s` iff some r has B_reverse(q,r) and a reverse pop
  `r --a--> s`.
- `control q --a--> suffix z` iff some r has B_reverse(q,r) and
  `Attachment(r,a::z)`.
- `suffix (a::z) --a--> suffix z`, and no other suffix transition.
- `control q` accepts iff some r has B_reverse(q,r) and Attachment(r,[]).
  `suffix z` accepts iff z is empty.

Its state language satisfies the exact derivative identity

    L(state, a::v) iff exists next in the finite universe,
       transition(state,a,next) and L(next,v).

For a control language factor y++z, either y is empty, and the first symbol
comes from the attached suffix, or y starts with a, and its first reverse pop
leaves the remaining factorization at the successor control. Conversely each
of these transitions reconstructs precisely one such factorization. A suffix
transition simply removes its first letter. The suffix universe is closed
under this removal. Empty input is handled by the displayed final test.
Induction on the read word proves this NFA recognizes L exactly. Combining
with the normal form proves L equals the FULL propagation closure.

This is semantic equality with the Python epsilon NFA, not equality of their
physical tables. Empty seeds, empty cuts, full cuts and empty untouched tails
are all retained. No reversed-suffix or left-concatenation substitution is valid.

### 4. Determinization and graph conversion

A deterministic state is a subset of the finite tagged state universe. It is
initially the singleton control for the chosen variable. On a letter, take the
union of all NFA successors. Accept if some member is final. Induction on the
word using the derivative identity proves that its residual language is the
union of the languages at its member states. There are at most 2^N subsets
for N entries of the finite tagged-state carrier, so explicit enumeration or
reachable-state exploration terminates. Duplicates in an enumerated list do not change the language.

For a finite DFA D, form a `Graph` on its state indices: final states are
products pointing to their two successors; nonfinal states are bottom.
For a specified root q whose accepted language is prefix-closed, graph
membership equals D's acceptance at every word. Proof by induction on the word:
a nonfinal root cannot accept ANY extension by prefix closure, so bottom is
exact; at a final root both systems follow the same child, whose language is
the corresponding prefix-closed derivative. No condition on unreachable DFA
states is needed. Applying this to the canonical closure yields exactly D_q
at every normalized variable root, even if C is inconsistent.

The full-powerset formal representation keeps nonfinal states as bottom nodes;
the Python implementation merges rejecting residuals into one bottom node and
explores accepting residuals. Those are language-equivalent representations.
Neither acyclicity nor a finite unfolding-depth assumption is used.

### 5. Original-input soundness and same address

When the supplied-word test succeeds, normalized graph values equal the
canonical closure, so the graph satisfies every normalized premise and
separates alpha/beta at the chosen w. Restrict graph roots along `Naming.old`.
The existing normalization theorem identifies the two query names with the
values of the original query expressions in this restricted graph valuation.
It also preserves all original premises. These are equalities of whole trees,
so the address remains EXACTLY w, not a renamed or merely existing separator.
Zero original variables and query-only product/bottom names are included.

### 6. Termination and completeness, not a guessed word cutoff

Each candidate test terminates: all seed/cut scans, balanced tables and
finite graph nonemptiness operations are finite. Every successful graph
conversion terminates on a finite powerset. Enumerate binary words fairly,
e.g. by finite length batches. A negative input has some finite successful
w by the canonical criterion and exact normalization. There are finitely many
batches before its length and finitely many words in each batch. Therefore
uncapped search reaches a success.

This argument also supports a constructive accessibility implementation of
unbounded search: the relation takes index i to i+1 only when batch i fails.
A known successful batch d proves accessibility of 0 by induction on d.
Recursion on that accessibility proof performs only Boolean batch tests; it
does not extract a countermodel by classical selection. Existential evidence
is used solely for the termination proof. Any classical axioms inherited
through erased correctness proofs must still be reported by dependency audits.

The total wrapper first evaluates the existing C081 entailment Boolean. A
positive result returns `none`; a negative result supplies the existence proof
for the search and returns its constructed graph. Hence `none` iff entailment,
and every negative input returns a valid regular countermodel. Positive inputs
must NOT be sent into the one-sided uncapped Python extractor alone. No
operational time, memory or word cap is part of this total mathematical algorithm.

### 7. Compatible certificate decoration

Given a finite graph/root valuation, append nodes bottom-up for the finite
original expression forest, leaving the old graph unchanged. Variables use
their original roots; bottom uses a bottom node; each product node points to
its two already assigned child nodes. The resulting finite map passes C084's
recursive embedding test, and old unfoldings are unchanged. Unused expression
arguments may map to any default node because C084 checks the actual forest.

For the finite enlarged graph, inclusion of two nodes is decided by traversing
their synchronous pair graph. A product/bottom pair is a mismatch; a bottom
left node has no obligations; a pair of products generates both child pairs.
A visited-pair set makes this an exact all-address test even with cycles.
If no mismatch is reachable, the visited relation is a finite simulation and
induction on addresses proves inclusion. Conversely the first mismatching
address gives a reachable mismatch. Taking all inclusion pairs therefore
computes a finite closed Boolean relation containing every true premise pair.
This explains completeness of certificate decoration independently of C084's
one-way soundness theorem. Its implementation/Lean connection must be stated
separately from the core graph producer, rather than silently assumed.

## Validation plan and boundaries

The owned checker will compare the actual pinned Python NFA with the new
presentation by COMPLETE finite subset-product language equivalence checks,
not only sampled words. It will independently check returned original-input
models using synchronous finite-pair reachability, verify the supplied word,
and exercise periodic infinite spines beyond the former five-shape library.
Literal acyclic stack closure tests have independently justified finiteness.
Any product-search cap is UNKNOWN. Positive/capped one-sided extraction is
never called ENTAILED.

Lean elaboration, pinned module builds, bundled `leanchecker`, all new named
axiom closures and runtime boundaries are separate gates. This container did
not initially have Lean/Lake; direct clone and the attempted pinned toolchain
download failed. Coordinator comment 5750364625 in #68 explicitly approved
the new branch-only workflow, with read-only repository permissions and no
shared workflow changes. Existing main CI does not validate unimported new
modules. Tests of a Python presentation do NOT execute or certify Lean code.

Outside the core theorem remain JSON parsing, variable-name/index transport,
source emission, OS process limits, resource-limit reporting and any unproved
certificate-decoration adapter. Finiteness of a graph is not finiteness of
its unfolding. No finite-tree claim, complexity improvement, novel priority,
C080 bound or change of constructor signature is made.

## Retained development evidence

The actual upstream Python blob is `b59c57174e24d00fdbe8dfca1c99337921adf88f`.
The checker uses seed `2026092068` and a 50,000-pair equivalence cap. Local
and initial CI runs complete 623 whole-language NFA comparisons and 238
whole literal-closure comparisons, with no incidental cap. Eighteen periodic
cyclic models and three boundary cases pass independent all-address original
syntax checking. All 775 former-library assignments tested for the first
three periodic families fail to supply a model. Intentional cap tests report
UNKNOWN; this is expected and is not an entailment answer.

At initial commit `17a57b6ac716ff2d7a20c35978a3192715b46182`, run
`35517118147` passes the pinned version and existing core build, but the new
module build fails because `universe` was used as a reserved identifier.
Kernel replay, axiom audit and native producer calls are NOT RUN at this
revision. Revision `f42836961f780df4000c01a3d52fde789d8c6b62`, run
`35517286238`, fixes the identifier and reaches the subset proof, but fails
on decoder rewriting and initial existential normalization. These failures
are retained in history. The next revision `b1fc4cf7287e16418cd5e24ed145a9f18da469a1`
makes those proof steps explicit; that revision was not an accepted checkpoint. Later checks are recorded below.

The intended Lean output is a freshly constructed graph, not an input graph
or a regularity assumption. This is a new epsilon-free/all-subsets algorithm;
no checked refinement of the existing optimized Python extractor is claimed.
The full C084 embedding/simulation decoration adapter is not implemented in
the new Lean modules. Independent mathematical review and runtime-erasure
readback remain separate from a successful source build.

## Checked original-input result

At source `8201846e70733c75567fc8e8b0e4f7342aa1ef0c`, the entire new
producer module, not just a supplied-certificate helper, passed the pinned
module build and bundled kernel replay. The exact public conclusions are:

- `produce_none_iff`: `produce G s t = none` iff `ExprEntails G s t`.
- `produce_sound`: every returned Model satisfies all original premises and
  separates the original expressions at that Model's finite word.
- `produce_complete`: every failed arbitrary-tree entailment returns some Model.

These have no caller-supplied regular graph, model, regularity assumption,
witness-length cutoff or certificate oracle. `Model` contains a newly computed
C084 Graph, roots for the original variables, and a finite word.
`modelForWord_correct` separately preserves an externally specified successful
word exactly. `canonicalGraph_exact` identifies every normalized root language
with the entire canonical closure, independently of satisfiability.

The final accessibility definition uses the standard well-founded relation on
accessible indices, with measure `Subtype.mk i acc`. This is the computable
interface to the same accessibility argument; the rejected initial attempt to
use the equation compiler's structural `Acc.brecOn` into Type is retained in
development history. It is not a change of search order or a bound assumption.

Run 35517920234 (artifact 10607761122) passed the explicit new-module build,
`leanchecker Subtail.RegularCountermodelProducer`, the full 73-named-declaration
axiom inventory, and five actual Lean runtime cases. Its downloaded artifact
SHA256 is `f5018d76c2e577ebaf399fa8b403a1c0ae7435d604144036e12e5daf6a9b40c4`.
The final source/checker/artifact pins are recorded in
`results/regular-producer-68.json`; documentation-only handoff changes do not
constitute another Lean execution.

The native cases are three total-wrapper negatives (closed terms, an
unconstrained variable, and an infinite left spine), a reflexive positive
returning none, and the normalized constructor on the alternating infinite
spine at word [true]. The alternating case exercises the supplied-word
constructor, NOT the full frontend/decision wrapper. All returned graph
valuations are checked at all addresses against their original-syntax test
problems by a separate finite-pair inclusion checker. The cyclic native graphs
have 32 and 256 nodes, including retained unreachable subset states.

The ordinary Python tests additionally produce 18 original-input periodic
cyclic models across six nonconstant periods, at separator depths 1, 2 and 4.
They exhaust 3,912 finite-product comparison states and 319 complete literal
configurations across the differential tests. The literal closures are finite
because every control transition strictly increases the control index; there
is no hidden stack-depth truncation. Regression tests are evidence about the
sampled cases, not a substitute for the all-input theorem.

### Trust and remaining obligations

The full named axiom inventory has no unexpected axiom and contains only
subsets of `propext`, `Quot.sound`, and `Classical.choice`. The top-level producer
and its correctness/completeness closures include all three. In particular,
classical existential reasoning is present in the termination/correctness
proof chain. `seekAcc` itself has only `propext` in its closure. No source
`sorry`, `admit`, `native_decide`, `noncomputable`, or `unsafe` occurs in the two
new implementation modules; this static observation is separate from the
completed kernel and runtime checks.

The type-checked executable model producer is the proved result. It is a new
Lean epsilon-free/all-subsets implementation, not a checked refinement of the
existing optimized Python epsilon-NFA/reachable-subsets implementation. The
ordinary language argument and differential experiments relate them, but no
Lean theorem asserts their implementation-level equality.

Automatic generation of C084's complete expression-map/simulation Certificate
record is NOT FORMALIZED here, although its ordinary construction is proved
above. JSON parsing, external names/indices, source emission, compilation and
serialization correctness, process limits and memory exhaustion are outside
the semantic producer theorem. A complete transitive generated-runtime audit
is NOT RUN. Independent mathematical reviewer readback is NOT RUN by this
worker; a request was posted, not treated as an acknowledgement or a completed
review. Integration onto a newer main revision needs its own pinned checks.

The source constructor can be exponentially large and the underlying complete
decision procedure can be expensive. No practical worst-case runtime or memory
bound is claimed. The harness uses 180 seconds per Lean command/case and a
50,000-pair differential-comparison cap; any exhausted cap is UNKNOWN. Explicit
positive-input one-sided extraction caps are UNKNOWN, not positive decisions.
The checked total wrapper instead uses C081 to handle positive inputs.

Finite graph size does not imply finite unfolding. In particular the reported
reachable cycles certify arbitrary regular infinite trees. No finite-tree
completeness or finite-tree certificate theorem is claimed. Issue 68 remains
open, and shared ledgers, manuscript, workflows and import aggregators remain
integrator-owned (apart from the expressly approved new branch-only workflow).

### Final pinned execution and limited generated-code readback

Final checked source: `b5dfd3576a0f9948d1f77ea9cfc215c08e85a77a`, still based
on the original `19b06d4fed9da635d9b911f0e908d04e4fc4b099` snapshot. Run
35518193660, artifact 10607761447, repeats all six version/build/kernel/audit/
runtime gates successfully. The actual downloaded artifact SHA256 is
`683a06c4c2261659611152b824224a31913fd23eae52dffcb958f7c62306b8aa`.
Every implementation/checker source hash in its receipt was matched to the
local authored bytes. The only subsequent handoff changes are this note and
the curated result receipt. These do not claim a new source execution.

The audit additionally executes `seek` with the first successful index 7 and
prints `REGULAR68 delayed_search PASS`. That is a delayed generic-search
regression, not a new original-input fixture. The five original/normalized
graph cases and their distinctions above are unchanged. In the receipt, the
label `native_producer` means actual Lean `#eval` evaluation, not a standalone
generated-C command-line executable. Standalone CLI packaging/testing is
NOT RUN. The ordinary `lake build` may reuse pinned cached dependencies; no
clean-from-empty-cache rebuild is claimed. The two new modules are explicitly
targeted and the producer module is passed to the bundled kernel checker.

The generated `RegularCountermodelProducer.c` has SHA256
`31f7c24ba80dad68975a2d1479fb3460431ce2acf611d70754a479a12495c399`;
`RegularLanguageGraph.c` has SHA256
`2dd29077e8e605a81650446b23d76a616946bf9a9bde492b23ac1c10fe9310c5`.
The former's `seekAcc`/`seek` definitions (lines 1918-1967) and
`findWord`/`produceNegative`/`produce` definitions (lines 2072-2157) were
read directly. The operational search body tests p(i), increments i when
false, and returns i when true. Proof-parameter wrappers forward without
using their proof argument. `produce` calls the existing entailment Boolean,
then either returns none or calls the actual search-and-construction code.
No Classical or sorryAx symbol occurs in this generated module. This is a
LIMITED source readback, not a proof of compiler correctness or an audit of
the complete transitive runtime/import closure. The latter remains NOT RUN.

All initial failures remain in branch history: runs 35517118147 and
35517286238 fail on the reserved carrier identifier and decoder proof;
35517371383 fails on the remaining initial-state witness; 35517515405
reaches the producer and reports five elaboration issues, including the
initial accessibility-recursion form; 35517788899 reports the final Boolean
proof-name error. Kernel/audit/runtime gates blocked behind those failures
are NOT RUN at those revisions, not inherited successes. Runs 35517920234
and 35518193660 are the successful complete checkpoints.
