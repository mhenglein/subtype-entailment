# Review of agent submissions, 2026-09-20

Session: `submission-review-20260920`. Base main: `9f4b95784a212c322c48a957b80645a1077543ed`.
Scope: all four open PRs and five additional issue handoffs found at review time.
[Coordination and ownership](https://github.com/mhenglein/subtail/issues/37#issuecomment-5750834857).
[Machine-readable evidence](../results/submission-review-20260920.json).

## Result and integration findings

The reviewed mathematical statements are acceptable within the scopes below.
No confirmed mathematical or implementation defect remains from this review.
This is independent agent review, not human refereeing or a publication-priority
claim. It does not promote shared claim records or authorize an overlapping
integration lease. No submission was merged or changed in this review.

Two concrete integration changes are needed before these proof additions become
maintained main-branch results:

1. **P2: include new proofs in continuing CI.** The new compiler, producer, and
   F workflows restrict pushes to their worker branches; the top workflow adds
   a PR trigger but still excludes main pushes. The existing default import,
   explicit-build and audit lists omit these new modules. A green default Lean
   job therefore does not cover all these additions. This was confirmed by the
   fresh combined run: the explicit compiler/top build compiled modules that
   the preceding default build had not built. Integrate explicit build, kernel,
   axiom and native checks, with main and PR dependency triggers. Preserve the
   scoped author workflows as history or replace them deliberately.
   Locations: [compiler workflow, lines 3-11](https://github.com/mhenglein/subtail/blob/db0a6d3505e93ff6bc51a8d89fcb52fb05adfe0f/.github/workflows/smaller-compiler-astra.yml#L3-L11),
   [producer workflow, lines 5-24](https://github.com/mhenglein/subtail/blob/049aa110cf13688d4058b1cbecf80aa0fc3a7fb6/.github/workflows/regular-producer-68.yml#L5-L24),
   [top workflow, lines 5-14](https://github.com/mhenglein/subtail/blob/0eff4818d990821fd1c08f704a2392f2d0047cf5/.github/workflows/explicit-top-dual-projection.yml#L5-L14),
   [F workflow, lines 4-10](https://github.com/mhenglein/subtail/blob/6aa7047cc6cbccd44c64223209b7563cf2824b8e/.github/workflows/f-only-astra.yml#L4-L10).
2. **P2: replace the F workflow's historical dependency overlay when integrating.**
   Its hash-checked secondary checkout is valid evidence for the submitted
   branch. After integration, copying that old compiler over the checked-out
   compiler would test the historical dependency rather than the combined tree.
   Land the reviewed compiler first, then build the F bridge against that actual
   tree. Keep the immutable original receipt for provenance; remove the overlay
   from ongoing validation. [Exact overwrite, lines 27-41](https://github.com/mhenglein/subtail/blob/6aa7047cc6cbccd44c64223209b7563cf2824b8e/.github/workflows/f-only-astra.yml#L27-L41).

These are integration gates, not criticisms of the agreed branch-only author
scope. Workers were explicitly told not to edit shared CI or import lists.
The integrator must coordinate those shared writes.

## Disposition of each contribution

“Accept” means the stated contribution survived this review. It does not mean
the whole parent issue is complete, a merge occurred, or all broader claims hold.
Full commit pins, file hashes and commands are in the JSON receipt.

| Submission | Reviewed head | Disposition | Remaining boundary |
|---|---|---|---|
| [PR #75: function variance](https://github.com/mhenglein/subtail/pull/75) | `4ed2fb67458f` | Accept ordinary characterization and obstruction | General function decidability/undecidability remains open; #74/#72 do not close |
| [PR #76: raw diagnostics](https://github.com/mhenglein/subtail/pull/76) | `986e34b4b61a` | Accept diagnostic tool and limited evidence | No optimization; six-variable complete query remains UNKNOWN; #66 stays open |
| [PR #77: graph-only preimages](https://github.com/mhenglein/subtail/pull/77) | `910e3071eab4` | Accept ordinary theorem for the stated schema | No full generic compiler implementation, generalized Lean proof or priority claim |
| [PR #78: smaller compiler](https://github.com/mhenglein/subtail/pull/78) | `db0a6d3505e9` | Accept exact existential compiler contract and retained-output bound | Continuing CI and explicit owner handoff needed; old compiler's universal bound remains false |
| [#69: F-only bridge](https://github.com/mhenglein/subtail/issues/69#issuecomment-5750572384) | `6aa7047cc6cbc` | Accept checked original F theorem | Depends on reviewed #78 source; optional FinishPlus proof route is not fully Lean-composed |
| [#68: regular producer](https://github.com/mhenglein/subtail/issues/68) | `049aa110cf13` | Accept total original-input producer core | Author handoff, continuing CI, full Certificate adapter, Python refinement and JSON boundary remain separate |
| [#70: hardness](https://github.com/mhenglein/subtail/issues/70) | `371b97c40d53` | Accept ordinary logspace reduction and PSPACE lower bound | Arbitrary and regular bottom/product trees only; no finite-tree transfer or matching upper bound |
| [#71: explicit top](https://github.com/mhenglein/subtail/issues/71) | `0eff4818d990` | Accept ordinary decision reduction and selective checked lifting | Full labelled-tree identification and expression-level algorithm are ordinary proofs, not full Lean implementation |
| [#72: ternary/fixed arity](https://github.com/mhenglein/subtail/issues/72) | `3fca2e8bf8a0` | Accept ordinary total reduction for fixed positive arity | No polynomial bound, finite-tree transfer, complete translator or new generalized Lean theorem |

## Mathematical readbacks

### Smaller compiler and original F

The compiler keeps the original finite diagram enumeration and semantics, then
filters diagrams by at most `a + S` active coordinates per physical interval.
Coverage chooses product-simple atom runs under one common assignment and one
common generated extension. The count injection keeps repeated traversals and
coordinates; it does not quotient equal origins or equal observer controls.
Zero-length forward pieces contribute tests without an emitted interval item.

`SmallerCompilerAstra.closureFor` has the required `ClosureFor I (preSmall I)`
type. Every retained clause obeys the original `64*k*T^(2*T+2)` weight bound.
This repairs the existential compiler contract with a different compiler. It
does not erase the counterexample for every output of the old compiler.

`FOnlyCompilerBridge.original_F` says, for every `Instance k` with terminal
finals, that witness existence is equivalent to existence of a witness of
length at most `FOnlyAstra.originalF k`. It has no caller-supplied compiler,
coverage hypothesis or witness bound. The bridge extracts the actual retained
diagram and uses bounded joint reconstruction; a clause-size bound alone would
not suffice. The recurrence is the original one, including `F(1)=0`, `F(2)=6`
and, for `k >= 2`, the factor `2*(k+1)` times the original growth product.

The compiler source at the PR head is byte-identical to checked source
`acf0524ffdbc9f407797b68b8953a39e1f79cf5d`, SHA-256
`9d23d5922c627708bb62f6f1d68059870c4566c6ef7aa8bd6384383cfe90ce05`.
The F bridge's complete checked route uses that dependency. Its alternative
FinishPlus argument must remain separately labelled: finishing at an internal
initial-control vertex need not be a first return to the current endpoint.

### Regular countermodel producer

The finite-seed reachability normal form is a union of reverse-pop languages
followed on the right by seed suffixes. The implementation enumerates finite
suffix attachments, builds an epsilon-free NFA, and proves its derivative
identity in both directions. Determinization and prefix-closed graph pruning
give `canonicalGraph_exact` at every normalized variable and finite word.

`produce G s t` takes original expressions and premises and returns an optional
finite graph with original variable roots and one separating word. It receives
no proposed graph or regularity hypothesis. The positive C081 branch returns
none; the negative branch searches finite length batches. Existence supplies
termination accessibility, not a noncomputable choice of witness. The soundness,
completeness and `none`-iff-entailment declarations match that interface.

The whole axiom closure includes `Classical.choice` through proofs. Source and
generated C readback show the inspected producer/search entry points erase those
proof arguments and execute the test/enumeration loop. This is a limited runtime
readback, not a transitive compiler/runtime correctness proof. Four negative
native cases and one positive case passed independent graph checks, including
cycles and a nonempty separating address. The complete C084 Certificate record,
the existing optimized Python producer and JSON serialization are not silently
certified by this new core.

### Hardness and the Henglein-Rehof source gate

The marker context is `H(X,Y)=((X*Y)*bottom)`, with codes `0->00`, `1->01`.
The recursive reference premise forces the proper regular language
`K=code({0,1}*){epsilon,0}` into its reference variable. For universal all-final
NFAs, an arbitrary-model run argument excludes every first illegal `code(w)1`
address. This direction does not assume values lie in the encoding's image.
For a missing word, the simultaneous regular assignment
`X_i = K union UNION_{u not in L_i} code(u){0,1}*` satisfies every edge constraint
and supplies a separator. Epsilon edges and the always-satisfiable source case
are covered. Output size is `n+2` variables and `m+1` depth-two inequalities;
construction is logspace. The reference forces an infinite tree, so this is
not a finite-tree hardness reduction.

The author-PDF access gate is now independently discharged for the imported
fact. I inspected rendered published pages 621-623 of Henglein and Rehof,
*Constraint Automata and the Complexity of Recursive Subtype Entailment*
(ICALP 1998), [author PDF](https://hjemmesider.diku.dk/~henglein/papers/henglein1998a.pdf).
SHA-256: `6da53bb92428595af33d2466e71a8436cd43c41d750f75f010e909780d795d39`.
Section 4 explicitly states CLOSED-UNIV PSPACE-completeness for any nontrivial
alphabet and immediately chooses a two-letter alphabet. Page 622 confirms the
transition orientation, recursive reference and top-labelled negative case.
Page 623 confirms the bottom truncation glyph and one-sided finite reference;
that finite-tree argument is not imported into the new reduction.
The [institutional record](https://researchprofiles.ku.dk/en/publications/constraint-automata-and-the-complexity-of-recursive-subtype-entai/)
also confirms authorship and publication metadata. No new priority search is
claimed here.

### Explicit top

The two observations are non-bottom addresses `P` and non-top addresses `Q`.
Equivalently use `P` and the top right ideal `H=complement(Q)`, with `H` contained
in `P`. This correspondence handles totalized leaf observations and reconstructs
actual labelled trees by stopping below bottom/top. Observation addresses need
not all be actual nodes; the note preserves that distinction.

The essential proof is universal lifting, not merely projection of a model.
The least forced-top language is included in every positive projected model
and disjoint from every negative projected model. Existence of one negative
model therefore makes every positive model lift; duality gives the converse
projection lift. Product-root exclusion is essential and follows from the
opposite model's forced product roots. Both projections share all named input
variables and product equations. Thus satisfiability requires both projections;
entailment is vacuous if either is unsatisfiable, and otherwise requires both
projected entailments with the negative direction reversed. At most four C081
calls suffice. The selective Lean module checks the language-level argument;
the full original labelled syntax and normalization remain ordinary mathematics.

### Ternary and fixed positive arity

The transfer goes through normalized push/pop summaries, not homomorphic
expression substitution. The forced-closure SAT guard is needed before
identifying separation with summary witnesses. The binary coding must preserve
strong absorption at all physical states, including unreachable states.
Partial codewords are safely completed, not blindly truncated. The recorded
`01 -> 010` example explains why that distinction matters.

The final total reduction uses the existing binary C029 decision, then C031
terminalization and C030 realization. Their current declarations have the
claimed hypotheses and directions, including arbitrary-model reconstruction and
same-word separation. Source inconsistency and the infinite-witness branch
produce explicit fixed outputs. C029 is part of the reduction's runtime, so
small emitted constraints do not establish polynomial runtime. The independent
Python component checks passed, but the complete translator and actual C029
execution of the generalized pipeline were not run. No finite-tree transfer
is inferred.

### Graph-only preimages and function variance

The graph theorem preserves one decorated generator shared across all atoms.
Its relational-copy semantics includes every permitted mismatch edge. Physical
marks, repeated interval coordinates, origin aliases and zero-length paths stay
distinct where needed. The bounded-portal result requires its fixed attachment
interface. The checker exercises components, not the complete generic compiler.
One reviewer queried an initial-End case. Re-reading the first-emission clauses
resolved it: `f=h_0` is separate from the first marked origin `z_0=h_1`; only
positive intermediate origins are required to be non-End. The reviewer withdrew
that finding. It is not an outstanding counterexample.

For functions, the active signed-path characterization and guarded Horn closure
preserve common active prefixes. Node-inclusion least closure is distinct from
a subtype-least model. The two-model example refutes additivity and therefore
the stated fixed additive existential-reachability encoding. It does not rule
out general reductions or settle function entailment.

### Diagnostics

The raw-summary harness is unchanged from native-tested `f8180b199721679dca8e4bd6df6b5ab420516f5d`.
This review reran its self-test and inspected the process-completion guards.
The existing [native execution receipt](../results/issue66-execution-20260920.json)
is reused at its actual revision: all eight `n=3` modes passed; the complete
`n=6` baseline and phased query stayed UNKNOWN under 20 seconds. An emitted end
marker from a killed process correctly remained UNKNOWN. CPU seconds and peak
RSS were unavailable. Separate probes are not additive costs or speedup evidence.
The conditional immutable-row-sharing identity is coherent, but no optimized
backend or all-input refinement theorem is supplied by PR #76.

## Review roles and execution evidence

The parent independently reviewed the producer, top, hardness, ternary and
diagnostic arguments and ran all new execution checks. The read-only
`publication_proof_review` reviewer checked compiler coverage/counts and the
F bridge against their dependencies. The read-only `historical_pr_review`
reviewer checked graph and function statements. They read the submitted proofs;
these are independent readbacks, not independently invented proofs. No model
diversity or human review is claimed. The compiler/F reviewer also completed a bounded second readback of the top
representation, lifting and vacuity proof, with no remaining mathematical
finding. Its final paper presentation should spell out the coinductive-order
and finite-naming correspondence. These presentation details do not change
the declared ordinary-versus-Lean boundary.

Execution used one fresh Linux AArch64 checkout, Python 3.13.14 and Lean 4.33.1,
with separate build/output directories. It overlaid 41 byte-exact, disjoint new
files onto main `9f4b957`; original tracked files stayed unchanged. This is a
manifest-pinned combined tree, not a fictitious commit containing the additions.
All file hashes were compared with their immutable source Git objects.

Nineteen scheduled check steps passed, plus the separate native compiler guard.
These include nine Python experiment invocations, the producer's default and
explicit builds/kernel/native checks, explicit compiler/top builds and kernel
replays, both F module checks and kernel replays, and the compiler/top audits.
The audits cover 22 compiler, 29 top, 73 producer/language and 26 explicitly
printed F declarations. Proof dependencies used only standard allowed axioms.
Seven deterministic author receipts replayed identically after excluding only
environment and elapsed-time metadata; the additional compiler repository
comparison also passed. Intentional capped searches remain UNKNOWN inside
passing harnesses. Hard-coded author provenance strings in some harness outputs
are historical; the outer receipt records the actual combined-checkout context.

The entire broad CI matrix was not freshly rerun on this overlay. Current main's
[Lean run](https://github.com/mhenglein/subtail/actions/runs/35518360794) passed
at `9f4b957`; the four PRs' existing completed non-skipped checks also passed.
Those are separate revision-pinned observations. Skipped writeback jobs do not
count as passing mathematical checks. #67/E061 was already reviewed and
integrated in the preceding checkpoint and is not reclassified as complete here.

## Handoff and recommended integration order

1. Claim the shared integration scope in #37 and obtain the compiler author's
   explicit handoff. Integrate #78, then the dependent F bridge, wiring their
   continuing checks against the actual tree. Reconcile #69/C080 carefully;
   retain the old universal-bound refutation and the distinct C082 result.
2. Integrate #70 and #71 with precise ordinary-versus-Lean labels, then update
   the paper and lower-bound/extension ledgers in that same integration episode.
3. Obtain the #68 author's final release and integrate the verified producer
   core with continuing CI. Keep certificate decoration and the practical CLI
   boundary as named remaining work. Integrate the fixed-arity result separately.
4. The three independent research/diagnostic PRs #75/#76/#77 can be integrated
   separately once their exact scope is recorded. Keep #66, #72 and #74 open
   for their broader outstanding goals; none supplies a general function solver
   or a completed performance target.

PR #76's author explicitly released the three paths in #66 comment 5750437070.
Later parent summaries that still list that author as active are stale, not a
renewed author claim. Reconcile the ownership table during integration. The
compiler and producer's still-unreleased author scopes are not taken over by
this review. Re-read all child comments and source heads before any publication.

Only this new note and receipt belong to the review branch. Existing sources,
ledgers, paper, workflows, author workspaces and stashes were not changed.
Source branches and failed attempts remain intact. The completion comment in
#37 releases this review/output scope; it does not release another author's
work. Licensing and authorship remain deferred by the owner.
