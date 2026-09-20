# Publication, solver and extension-proof plan

Date: 2026-09-20. Reviewed baseline: `0ef097576686a5d3886fb89cbce504d03dc0bfa9`.
Coordination: [#54](https://github.com/mhenglein/subtail/issues/54), integration
[#37](https://github.com/mhenglein/subtail/issues/37). Related workstreams: A010/A018.

**Planning baseline:** the initial review at `c360966` proposed the programme
below. Later execution is recorded separately in the update below; completed
solver work does not make the manuscript or extension programme complete.
The previous [programme](POST_C081.md) produced a research checkpoint. A
publication-ready paper, broadly useful solver and new signature theorems
require further work. Implementation ownership remains in the registry and
future scoped issue claims; this document assigns no workers or paths.

## September 20 update: complete extraction and checked certificates

Issue #57 supplies a complete ordinary canonical NFA/finite graph extractor
and [C084](claims.md#c084), a Lean certificate soundness theorem for original
expressions over arbitrary trees. `--verify-certificate` compiles a particular
non-entailment proof using `by decide`. The new alternating-spine example
requires a graph outside the old fixed library. [Construction and proof boundary](../notes/2026-09-20-regular-countermodels.md)
and [source-pinned validation](../results/regular-countermodels.json).

This completes usable extraction with a checked certificate interface. It
does not complete the stronger plan below to formalize the NFA construction,
its graph conversion and all producer-completeness implications in Lean.
JSON/source emission and extraction remain ordinary Python. E055's remaining
decision timeouts are unchanged. The next mathematical target is the finite-tree
reduction below; the next performance target remains profiling those timed-out
cases. Neither is assigned by this update.

## Execution update: standalone paper rewrite

The [revised manuscript](../paper/manuscript.md) now follows the narrative and
notation plan below. It includes the complete shared-word terminal preimage,
coverage, reconstruction and termination arguments, worked diagrams, and the
ordinary regular-model and guarded constant-free transfers. Conventional
numbered results, a bibliography and integrated Henglein–Rehof attribution
replace internal research administration. The detailed proof map, source pins,
licensing status and review evidence remain outside the manuscript.

The [rewrite readback](../notes/2026-09-20-paper-rewrite-readback.md) records the
manuscript-first mathematical review, refreshed HR97/HR98/NP99/NP03 comparison,
corrections, source checks and PDF validation. These are bounded agent reviews,
not human peer review or a global novelty search. No new Lean proof, extension
theorem or performance result is claimed by the rewrite. Author information
and licensing remain owner-deferred. Issue [#56](https://github.com/mhenglein/subtail/issues/56)
contains the exact integration scope and release.

## Execution update: cached solver proof

The [finite saturation and cached solver](../notes/2026-09-20-fast-summary.md)
now has an unconditional equality proof against the original C081 Boolean.
This implements the sound shortcuts and a finite saturation path from items
2–3 of the solver plan. The complete fallback still uses its old representations.
The [separate source readback](../notes/2026-09-20-fast-summary-readback.md)
found no correctness blocker. The first acceptance target is met: all 26
full-expression cases complete
under the same cap, and the matched total improves from 24/38 to 33/38.
Five unchanged raw probes and three deeper generated cases remain UNKNOWN.
The note and its [native receipt](../results/entailment-fast.json) preserve those
limits. Constructing only needed summary states, complete countermodel
extraction and extension proofs remain separate tasks. The paper revision is
recorded above. The review findings below describe the original
planning baseline and preserve its earlier measurements.

## What the review found

- The manuscript contains a substantial ordinary argument, including the
  terminal construction, but also internal claim IDs, checkpoint details,
  validation logs and repository-history language. Its related-work section
  has no direct discussion of the Henglein–Rehof 1997/1998 papers or conventional
  bibliography. Its diagnostic figures also predate the latest solver work.
  A substantive rewrite and a manuscript-only mathematical review are needed.
- Matched E054 evidence is **24/38 completed, 14 UNKNOWN**. Only 17/26
  full-expression inputs complete; both improvements over the original
  implementation occur among raw-backend probes. Even bottom inclusion,
  transitivity and product covariance time out in the full-expression route.
  This is a real usability failure. It does not refute the correctness or
  termination theorem, which does not promise completion under these caps.
- The regular-countermodel transfer has a reviewed ordinary proof. Finite-tree
  answers can differ from arbitrary-tree answers. Explicit top, other arities,
  multiple constructors and contravariance have separate proof obligations.
  A feasibility study does not discharge them.

Evidence: [manuscript](../paper/manuscript.md), [matched receipt](../results/entailment-lazy.json),
[extension proof and obstructions](../notes/2026-09-19-post-c081-extensions.md),
[novelty matrix](../notes/prior-work/novelty-matrix.md). These are source and
saved-result readbacks, not fresh Lean builds or new benchmark executions.

## 1. Rewrite the paper around the mathematics and its literature

The first rewrite is recorded above; retain these criteria for further review.
Keep the current exact
bottom/product arbitrary-tree theorem as the paper's principal result. Do not
delay its exposition until explicit top or every extension is settled.

**Scientific narrative.** Introduce the entailment problem, its significance,
the historical results, the precise missing case addressed here, and the
central proof idea before presenting implementation details. Give ordinary
definitions, numbered theorems and consistent notation. Explain normalization,
canonical separation, stack summaries, the two decision branches, and their
composition. Give worked positive and negative examples.

The terminal argument needs a complete definition of its finite diagrams,
shared word parameters, interval generators and acceptance conditions. Prove
soundness, coverage of every required witness, reconstruction and termination
separately. A Lean declaration name is not an ordinary proof. Every imported
result needs a precise citation and a mapping of its hypotheses to our objects.
Include the corrected quantitative result only with its exact scope; preserve
the unresolved original bounds in the research records.

**Henglein–Rehof as a central part of the account.** Use primary-source
citations in the introduction and at the relevant technical constructions,
with a full bibliography. The comparison must retain these boundaries:

| Source | Result to credit | Boundary for this paper |
|---|---|---|
| Henglein–Rehof, LICS 1997, Theorems 4.7–4.8 and Corollary 4.9 | coNP completeness of structural simple-type entailment over a nontrivial base lattice; hardness already with a binary covariant constructor | Structural finite simple types are not our nonstructural arbitrary-tree domain. |
| Henglein–Rehof, ICALP 1998, Section 3 and Theorems 1–2 | Constraint automata; PSPACE hardness of nonstructural entailment over both finite and infinite trees | The nonstructural domain includes explicit bottom and top. A syntactically product-only hard instance does not remove top from its valuations. |
| Henglein–Rehof, ICALP 1998, Theorem 5 | PSPACE completeness for structural infinite-tree entailment over a lattice of constants | This is a different theorem from their nonstructural hardness result. Their paper leaves the matching nonstructural upper bound open. |
| Niehren–Priesnitz, Information and Computation 2003 | Automata and word-equation characterization of nonstructural subtype entailment | Explain the exact semantic mapping and which constructions are inherited or adapted before claiming a new step. |

Primary sources: [HR97 DOI](https://doi.org/10.1109/LICS.1997.614961),
[HR97 proceedings record](https://lics.siglog.org/archive/1997/HengleinRehof-Thecomplexityofsubt.html),
[HR98 paper](https://hjemmesider.diku.dk/~henglein/papers/henglein1998a.pdf),
[HR98 proceedings record](https://link.springer.com/chapter/10.1007/BFb0055089),
[NP03 record](https://www.ps.uni-saarland.de/Publications/details/SubTypeEntailment:02.html).
Refresh forward and backward citations before finalizing novelty language.
Historical statements about what a paper left open do not establish current
global open status. Do not transfer PSPACE hardness to the exact top-free
domain without a separate proof; C083's existing NL lower bound remains distinct.

**Remove internal material from the manuscript.** Move task IDs, issue links,
commit hashes, workflow receipts, abandoned approaches, audit commentary and
licensing administration to the repository or supplementary artifact. Retain
a short conventional formalization section and an artifact citation; keep the
detailed declaration map alongside the artifact. Use a bibliography, theorem
cross-references and a reproducible publication layout. Keep the requested
author/affiliation placeholders; do not invent attribution or grant a license.

**Acceptance:** a reader can reconstruct the decision proof from the paper and
its cited mathematics without reading Lean or internal notes. An independent
review first sees the manuscript alone, checks every construction and difficult
implication, and then compares the statements with Lean. Resolve identified
gaps before calling the manuscript ready. Build and inspect every PDF page;
check references, notation, examples and source correspondence. Cosmetic
cleanup alone does not meet this requirement.

## 2. Make the solver pass basic end-to-end use

Use wb-marcus for isolated builds and matched measurements. Preserve the E054
20-second wall/CPU and 16-GiB address-space caps, one Lean thread, fixture
identities and original receipts. Report frontend, normalized and raw-backend
results separately; never compare timings from different hosts as a speedup.

1. Instrument normalization, balanced closure, summary construction, terminal
   query materialization and witness extraction. Record time, peak memory,
   state counts and cache hits per phase. The tiny raw-reflexive case already
   exposed query materialization; it does not establish one bottleneck for all
   remaining cases.
2. Add sound early proofs for bottom inclusion, transitivity and covariance.
   A failed shortcut falls through to the complete decision procedure. Checked
   countermodel candidates may supply early negative answers; a Python-only
   checker must retain its separate trust label until its correctness is proved.
3. Replace enumeration of all `2^(n*n)` balanced-relation tables with least
   closure by a worklist. Prove soundness, closure, leastness and termination
   after at most `n*n` new pairs; use these to prove equality with the reference
   Boolean. Compute reusable forward/reverse tables once. Ordinary finite
   graph reachability also should not enumerate all invariant subsets.
4. Construct only needed summary states rather than all `4^n` subset pairs.
   Prove preservation of the accepted witness language, endpoint flags and
   absorption properties. Use shared or lazy query representations where
   profiling justifies them, with separate equivalence proofs.
5. Return a separating path and a complete finite graph countermodel on
   negative answers. Connect extraction to the regular-countermodel theorem
   below; validate the original expression constraints, not just their normalized
   proxy. Bounded extraction failures remain explicit incomplete explanations.

**First acceptance target:** all 26 existing full-expression cases complete
correctly within the same 20-second cap, with no regression on previously
completed cases. Publish the raw-backend results as well. Add generated scaling
families and independent literal/certificate checks so the target cannot be met
by special-casing the fixed suite. Prove optimizations preserve the decision;
run the pinned build, kernel replay and runtime dependency audit. Continue
returning `UNKNOWN` whenever a resource cap stops the computation. Passing this
initial target is progress, not evidence of broad practical scalability.

## 3. Pursue extension theorems, with explicit proof milestones

### Regular trees and effective countermodels: nearest completion target

Turn the existing ordinary proof into a checked constructive theorem:
non-entailment over arbitrary trees yields a finite graph countermodel, and
entailment over arbitrary trees equals entailment over regular trees. Prove
the finite-seed reachability NFA construction, conversion of its prefix-closed
language into a tree graph, and preservation under expression normalization.
Expose an executable extractor, then connect it to the solver. Regular-model
existence is already in the literature; identify the verified construction
and implementation contribution without claiming the existence theorem as new.

### Finite trees: test a specific reduction, not unchanged answers

The zero-spine example refutes using the same unmodified input and answer for
finite trees. It does not refute a computable reduction. Investigate this
candidate, using the existing stack factorization:

For a normalized system with propagation system `W`, let
`L(q,m) = {c : Pop_(W^op)(q,c,m)}` and
`H = {m : L(q,m) is infinite for some q}`. The languages `L(q,m)` are regular. Add
denials `x_m <= bottom` for every `m` in `H`, obtaining `C_fin`. Test and prove,
or refute, the proposed equivalence

```text
C entails a <= b over finite trees
  iff C_fin entails a <= b over arbitrary trees.
```

The intended intermediate statement is: closure of a finite seed set is
finite exactly when it reaches no control in `H`, at any stack. Infinite
`L(q,m)` expands any reached `(m,z)` to infinitely many `(q,c z)`; conversely,
minimum-stack factorization expresses closure as a finite union of such
languages with fixed suffixes. Prove orientation, both inclusions, and that
adding denials changes neither propagation nor forced roots. Then prove both
model-transfer directions and finite-value preservation under normalization.
Define finite trees explicitly and prove that finite product-node sets represent
exactly those trees, so that the reduction targets the intended semantics.
NFA infiniteness must detect a productive cycle consuming a letter, not just
an epsilon cycle. This is a **candidate argument awaiting focused verification**,
not an established extension or a new claim-ledger entry.

### One constructor of another fixed arity

Target bottom plus one covariant constructor of each fixed positive finite
arity, over arbitrary trees. Audit the stack alphabet, safe-extension split,
terminal rank and diagram construction for dependence on binary branching.
Establish the regular-countermodel transfer for that arity before claiming a
generalized decision theorem.
Parameterize only after the ordinary argument works. A binary encoding alone
does not prove transfer: arbitrary valuations must satisfy its representation
invariant. Keep multiple distinct constructor labels outside this theorem.

### Explicit top: a substantive new proof project

Target the exact enlarged bottom/product/top tree domain from the extension
note. Top is a nullary label, distinct from the full infinite product tree.
The objective is a complete decision theorem, not another feasibility report;
its success is not yet justified by the present proof.

Begin with the exact root-shape lemma

```text
Product X Y <= Z
  iff Z = Top or exists Z0 Z1, Z = Product Z0 Z1 and X <= Z0 and Y <= Z1.
```

Prove its dual for a product on the right. The first substantial milestone is a
label-aware separation theorem and an effective finite witness representation
with both directions of correctness. A product below a variable allows that
variable to be product **or top**, so the present product-node propagation is
insufficient. State how label choices remain consistent across repeated
occurrences. Then prove finite coverage and termination, or exhibit an
obstruction to the proposed representation and
change the route. Keep a genuine undecidability route available. Test the
known failed top-to-Omega/bottom reductions and constant-free domain example
before formalizing substantial machinery. Do not count a conditional theorem
with an unproved representation hypothesis as solving the extension.

Multiple constructors and contravariant arrows follow as separate projects
after this label analysis. Each needs exact order rules and its own reduction
or proof; neither follows from changing the alphabet or flipping an edge.

## 4. Review, integrate and release in stages

The first manuscript rewrite and measured closure optimization are recorded
above. Next finish checked regular extraction and test the finite-tree reduction,
while profiling deeper solver cases and inviting further mathematical review.
Audit fixed arity next. Pursue explicit top
under its own proof outline, without making the current paper wait for it.

Use a separate manuscript referee, an optimization/proof author and an
adversarial extension reviewer when their scopes are independent. Agree
interfaces and one writer per path. Agent review is useful; model agreement
does not replace a checked implication. No particular model family is needed
before the work can start, and no external human review is a prerequisite for
the next research iteration.

Publish separate evidence for manuscript completeness, semantic correspondence,
formal verification and performance. Update the theorem map, novelty matrix,
README and current records only after the corresponding changes pass review.
Keep the original checkpoint intact and create a new stable version for the
revised paper and artifact. Licensing remains pending and author information
remains placeholder text until the owner supplies it.

The original planning baseline used parent manuscript/code/receipt readback, a separate bounded
primary-source review of HR97/HR98, and a separate extension-target review.
Those checks were for planning; they were not a fresh review of every line of
the decision proof or a verification of the proposed finite-tree theorem.
The later paper review has its own scope and evidence linked above.
