# Complete regular countermodels and checked certificates

Date / author: 2026-09-20, countermodels-20260920. A010/A018, C081, #57/#37.
Base: `25e5c124d4fc1dc3c31bcf13ab1b420d835c8639`.
Status: ordinary construction with source review and checked certificate
soundness (C084). Validation revisions and boundaries are recorded below.

## Exact target

For a finite original expression input over bottom and one covariant binary
product, with arbitrary-tree non-entailment, compute a finite directed graph
whose unfolding satisfies every premise and falsifies the query at a supplied
finite address. No finite-tree hypothesis is made. A resource cap returns
UNKNOWN for extraction; it cannot retract a completed C081 decision.

## Construction and route

1. Name each distinct expression subterm, with both product inequalities for
   each product name, and a denial for the bottom name. Original variable
   indices stay fixed. This is an ordinary exact definitional normalization;
   it need not duplicate Lean's occurrence table. Model restriction and unique
   expression evaluation prove both directions. The original-input checker
   must validate the returned graph independently.
2. Form the finite epsilon/push/pop system W from normalized constraints.
   Compute its least balanced relation by reflexive/epsilon initialization,
   composition and matching push/balanced/pop closure. The finite pair carrier
   proves termination. Reverse W by swapping each rule's direction and
   exchanging pushes with pops; compute its balanced relation too.
3. For each proposed address w, seed forced roots and every alpha-prefix of w.
   For every seed (p,u), every cut i, and each r in Pop_W(p,u[:i]), attach the
   fixed suffix u[i:] to r in the reverse-pop NFA. Its controls are W's states;
   balanced reverse pairs are epsilon edges and reverse pops are letter edges.
   Suffix states are disjoint from controls, accept only the empty remaining
   suffix, and never return to controls. From initial q the exact language is
   the union of L(q,r) followed by u[i:]. The suffix is on the RIGHT.
4. Minimum-stack factorization (existing checked StackReachability theorem;
   ordinary manuscript Proposition 12.2) identifies this language with the
   full canonical closure. Forced roots plus prefix seeds make it prefix-closed.
   Test denials by finite NFA reachability to a final state, and test that beta
   does not accept w. These are exact finite tests, not bounded stack search.
5. Enumerate finite binary addresses fairly. C081-negative input supplies some
   separating address, so one test eventually succeeds. Determinize only that
   NFA. Each reachable accepting subset is a product node, rejecting subsets
   map to bottom, and the two successors follow 0/1. Prefix closure ensures a
   rejected prefix cannot acquire an accepted extension. Restrict to original
   variable roots. This terminates and yields the promised countermodel.
6. Verify original premises and query failure using the independent finite
   pair-graph checker. A new Lean certificate checker will discharge its own
   soundness statement against ExprEntails. Python normalization, NFA extraction,
   JSON and process boundaries are not silently promoted into Lean proofs.

## Weakest obligation and falsification

We need one countermodel for a negative input, not a minimal graph or preservation
of all possible countermodels. Check root/empty cases, zero variables, bottom
names, repeated subexpressions, both stack directions, shared suffixes, denial
propagation, recursive alternating spines, and separators beyond the former
five-shape library. Compare NFA word acceptance with explicit finite closures
where a bound is justified, and independent direct graph checking everywhere.
A finite word cap is UNKNOWN even if every tested word fails.

## Review and remaining proof boundary

The ordinary regular-language route already appears in the reviewed manuscript.
A separate read-only reviewer will inspect the present construction and code.
The Lean worker owns only a new certificate module, not the canonical core.
The specific formalization target is certificate soundness for original finite
expressions; a fully Lean-verified regular-language extractor remains separate
unless its entire construction is actually checked. The opposing undecidability
route is already excluded for C081's exact signature, not for its extensions.

## Ordinary correctness and completeness argument

Let D_q be the product-address set assigned to normalized variable q. Naming
an expression adds its defining equations: D_bottom is empty, and a product
name has both inclusions with the product of its child names. These inclusions
force equality. Induction on expression syntax identifies every name with
its original expression's value. Thus restricting a normalized model preserves
all original premises and the query, and every original model extends to the
normalized system. Sharing equal subterms changes the number of names, not
this argument.

For W, the balanced table starts with identity and epsilon rules. Each round
adds transitive consequences and every pair p,q with a push p--a-->r, an
already balanced pair r,s, and a pop s--a-->q. Every added pair has a balanced
run, by concatenation and wrapping. Conversely, the usual first-return
induction on a balanced run decomposes it into precisely these operations.
This is the relation characterized by the existing
`StackSummaryFast.mem_balancedTable` theorem. The Python bitset table is a
separate implementation of that least relation. At most n² pairs can be added;
Warshall composition and a finite push/pop scan make each round effective.

In the reverse system the same construction yields B_rev. A pop machine starts
in the B-closure of p and, on a, follows one pop-a edge and then B-closure.
Hence its reached set after v is exactly {r : Pop_W(p,v,r)}. Allowing balanced
epsilon edges between pops in the reverse NFA gives exactly Pop_Wop(q,v,r),
including an empty consumed word and trailing balancing.

Fix one seed (p,u). Minimum-stack factorization gives an exact equivalence:

    (p,u) reaches (q,v)
      iff there exist i,j,r with
        u[i:] = v[j:],
        Pop_W(p,u[:i],r), and Pop_Wop(q,v[:j],r).

Here i and j include zero and the full word length. Put z=u[i:]. Reading a
reverse-pop prefix v[:j] from q reaches r; the attached path at r reads exactly
z and accepts. Conversely, every accepting NFA path enters one suffix path
from a control r and never returns to a control. Its prefix and suffix give
exactly this factorization and identify a seed. Thus the NFA language at q is
D_q, the full propagation closure of the finite seed set. Branches from distinct
seeds may share the same fixed-suffix path without adding a language: the
suffix state records the entire remaining suffix, and cannot switch back to
an unfinished reverse-pop branch.

Forced roots and all prefixes of the candidate w satisfy the hypotheses of
`CanonicalModel.derived_closed`. Hence every D_q is prefix-closed. The NFA
nonempty-language test checks whether a final state is reachable in its finite
transition graph, ignoring letter labels; every such finite path reads some
word. Requiring this to fail at every denied control proves the canonical
model safe. The final acceptance test requires w not in D_beta. Its inclusion
in D_alpha follows from the seed (alpha,w). The existing canonical-model
argument now supplies every normalized premise and the separating address.

Subset construction starts at the epsilon closure of each original control.
It records reachable accepting subsets and a single bottom node. On 0 or 1,
an accepting successor is another product node and a rejecting successor is
bottom. No rejected prefix has an accepted extension, by prefix closure of
D_q, so this pruning preserves exactly the original product-address language.
The finite powerset has at most 2^N states for N NFA states, so conversion
terminates. The returned graph may have cycles; these denote regular infinite
trees. Restriction to original variable roots and syntax evaluation recover
the original premises and query failure.

Finally, syntax-derived suggestions form a finite set. The subsequent
length-first enumeration visits every binary word outside that set. On a
non-entailed input the canonical separation theorem supplies a finite w;
it is therefore eventually visited. Every test and the successful graph
conversion terminates. This proves completeness of the uncapped algorithm
conditional on non-entailment. A capped implementation may return UNKNOWN;
a positive input need not terminate in this one-sided extractor. The total
workflow first uses C081 to decide which case it is in.

### Implementation and formal trust boundaries

The Python implementation is reviewed and tested ordinary code. Its graph is
independently checked against the original input, so no agreement with Python
normalization or the NFA construction is needed for certificate validity.
Finite pair-graph inclusion handles every address of a cyclic graph, not just
an unfolding depth. A successfully checked certificate establishes a negative
answer even if the extractor chose a different graph or separator.

The separate [certificate module](../lean/Subtail/RegularTreeCertificate.lean)
provides `check`, `check_sound` and `check_not_entails`. It checks every
related pair, every original expression recursively, every premise endpoint
and the supplied address. `check_sound` gives an explicit model satisfying
all original premises with the query false at that word. `check_not_entails`
then rules out universal arbitrary-tree entailment. This is C084.

The Python emitter adds nodes for original expression syntax, builds a finite
simulation relation by pair reachability, and emits a total expression-node
map whose unused cases default to zero. Lean only uses this map after recursive
validation over the finite original input forest. `--verify-certificate` also
emits the particular theorem `¬ ExprEntails input left right`, proved by
`check_not_entails ... (by decide)`. A true runtime marker alone is insufficient:
the complete process, including kernel validation of that proof, must succeed.
There is no `native_decide` in this proof.

No statement asserts a Lean-verified regular-language extractor or checked
completeness of Python normalization/search. The reviewed ordinary proof and
the Lean certificate guarantee remain distinct.


## Reproduce

```sh
python3 -m unittest discover -s scripts -p 'test_subtail.py'
python3 -m unittest discover -s scripts -p 'test_regular_countermodel.py'
python3 scripts/check_regular_certificate.py
(cd lean && lake build +Subtail.EntailmentFast +Subtail.RegularTreeCertificate)
python3 scripts/subtail.py examples/countermodels/alternating-spine.json \
  --timeout 60 --verify-certificate
python3 scripts/subtail.py examples/countermodels/alternating-spine.json \
  --check-model examples/countermodels/alternating-spine-model.json \
  --timeout 60 --verify-certificate
```

The default CLI deadline includes decision, extraction and optional verification.
The extractor runs in an isolated process group with Linux memory and CPU
limits. All platforms have a wall-clock deadline. Extraction has an 8 MiB result
limit; the emitter caps its relation matrix at one million entries. These are
operational limits, not mathematical cutoffs. Native decision and explanation
status stay separate. A resource failure never upgrades UNKNOWN to ENTAILED,
nor retracts a completed negative decision.

The three-node alternating example has roots x=1, y=2 and nodes
`[null, [0,2], [1,0]]`. Thus x is bottom × y and y is x × bottom. Its query
`x <= bottom × bottom` fails at `[1]`. No assignment to the five earlier fixed
graph shapes satisfies this input, as exhaustively checked in the regression.

## Validation and review

The separate construction reviewer read `3e41754` (extractor from `93bfffd`)
and found no semantic blocker; the exact scope and later invariant guards are
in [the readback](2026-09-20-regular-countermodels-readback.md). The parent read
the full certificate source from worker `7a3bcd3` before additive integration
as `a5d0ebc`. The graph interpretation, left/right order, finite simulation,
recursive expression map and original-input theorem match the intended C084
statement. Existing C081 proof sources and import aggregator are unchanged.

The worker's isolated Mac build, module kernel replay and native checks passed
at `7a3bcd3`, including 34 native certificates (15 valid, 19 invalid/tampered)
and 15 positive per-input kernel proofs. The parent runs the same full native
and instance-proof driver against the combined tree; its fresh receipt and
CLI readbacks are recorded below. The original proof's runtime definitions
are audited separately from erased proof terms.


### Fresh combined evidence

At `d63285292f78f06c1340a7bc2955777ae8317956` on isolated wb-marcus:

- PASS: new module build and kernel replay; all 24 declaration dependency
  closures; all 14 non-theorems avoid classical choice.
- PASS: 34 native certificate checks, including 19 invalid/tampered rejections;
  every one of the 15 valid cases also has a kernel-checked instance proof.
- PASS: 24 Python CLI/resource tests and 9 extraction tests. The latter use
  80 complete acyclic literal closures, 60 cyclic systems compared against
  independent unbounded predecessor saturation, all negative pairs among
  26 finite depth-three trees, and 120 independently witnessed cyclic inputs.
  Seeds are 5701, 5702, 5703 and 5704, as recorded with their individual suites.
- PASS: five actual CLI certificate proofs. Alternating spine takes 4.000 s,
  zero-variable input 1.997 s, zero spine 1.945 s, reverse query 1.947 s, and
  rechecking the supplied alternating model 1.040 s. These are single diagnostic
  timings including startup, not a broad performance claim.

The [machine receipt](../results/regular-countermodels.json) preserves exact
sources, commands, outcomes and per-input proofs. The earlier default core
build/kernel/differential suite passed at `93bfffd`; none of its source modules
changed later. Existing C081/default proof sources remain unchanged. The
source reviewer separately checked the certificate module at `a5d0ebc` and
found no semantic mismatch. Old E055 timeouts and measurements are untouched.

The next mathematical target is the explicit finite-tree reduction in the
publication plan. A fully Lean-verified NFA extractor is a separate possible
formalization target. No new workstream is automatically launched by this
handoff. Main CI is read back separately at publication; a pending or skipped
run is not recorded as a pass here.
