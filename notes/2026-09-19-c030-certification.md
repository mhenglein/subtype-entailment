# C030: kernel-checked direct terminal realization

> **September 20 integration update.** The unchanged proof sources now have an
> independent statement/source readback and fresh combined-tree validation.
> [Integration record](2026-09-20-repository-reconciliation.md). The dedicated
> workflow now covers main and semantic dependencies; the modules remain optional.
> Budget preservation is still a separate ordinary-proof subclaim. The handoff
> and pending-review wording below retain their original checkpoint scope.

Date: 2026-09-19. Workstreams A011/A013; coordination #37; prior review PR #46.
Session: ChatGPT c030-integration-certification-20260919.

**Result:** C030's always-satisfiable, same-word realization core now has a
complete Lean proof on the contribution branch. The accepting states must be
terminal; ordered flags, Bad, initial state and accepting set are otherwise
arbitrary. The construction uses exactly `Fin (2*k+1)` for its variable type.
The proof ranges over the original arbitrary, possibly infinite trees.

This is certification of the realization core, **not** formal certification
of the separate budget-preservation claim, a complexity equivalence, an
arbitrary-final converse, C029, or completion of the forward decision procedure.
Branch verification and main integration are separate statuses. The handoff
in #37 and the contribution PR identify whether this source has been merged.

## Provenance and exact checked checkpoint

- Original independent mathematical review input:
  `064fc7306b679bf607b91e7d8de259823f200c62`.
- The ordinary proof, independent checker, replay wrapper and historical
  evidence were integrated through [PR #46](https://github.com/mhenglein/subtail/pull/46)
  at main `7185b15140fbc629bf1825063d1652d4feb8a43f`.
- This isolated formalization branch, `lean/c030-direct-20260919`, starts from
  that integrated checkpoint. No existing source or shared record is changed.
- **Checked Lean source:** `44725541a67675e050d00a20ea6f684bb1c025f4`.
- **Successful execution:** [C030 run 35451614047](https://github.com/mhenglein/subtail/actions/runs/35451614047),
  job `105919641790`. Compilation, independent kernel replay, the complete
  declaration audit and the independent exact-tree regression all PASS.
- This final documentation update does not change the checked Lean or workflow
  source. Its later commit is a documentation checkpoint, not a relabelled
  fresh proof execution.

The earlier [complete direct review](2026-09-19-c030-independent-review.md)
contains both ordinary proofs, the separate saturation audit, all edge-case
analysis, exact clause count, and the counterexample obtained only by removing
terminality. This formalization implements that already-complete argument.
The implementing author performed the final source/statement readback; this
is **not** a second blind independent review of the new Lean source. No separate
reviewer was launched. Kernel replay is an actual separate checking step.

## Exact public statements

All declarations below are in `Subtail.TerminalRealization`.

```lean
def TerminalFinal (I : Instance k) : Prop :=
  ∀ q, I.final.get q = true → ∀ c, step I q c = none

def constraints (I : Instance k) : List (Constraint (2 * k + 1)) := ...

theorem realization_satisfiable
    (I : Instance k) (ht : TerminalFinal I) :
    Satisfiable (constraints I)

theorem witness_iff_separating
    (I : Instance k) (ht : TerminalFinal I) (w : Word) :
    Witness I w ↔ ∃ rho, Models (constraints I) rho ∧
      (rho (a I.initial)).nodes w ∧ ¬ (rho (v I.initial)).nodes w

theorem not_entails_iff_witness
    (I : Instance k) (ht : TerminalFinal I) :
    ¬ Entails (constraints I) (a I.initial) (v I.initial) ↔
      ∃ w, Witness I w
```

The ellipsis above abbreviates the already-implemented finite constructor,
not an obligation or a placeholder in the Lean source. Separation at w means
membership in the upper query tree and nonmembership in the lower query tree
at that same address; it does not assert that w is the unique separating address.

### Exact construction

The indexed copies are `a q = q.val`, `v q = k+q.val`, and `b = 2*k`, all
inside `Fin (2*k+1)`. Undefined children map to b. The finite list contains:

1. The denial `b <= bottom`.
2. Every upper clause `a_q <= A(delta(q,0)) x A(delta(q,1))`.
3. A lower clause `V(delta(q,0)) x V(delta(q,1)) <= v_q` exactly when q is
   nonaccepting, including nonaccepting terminal states.
4. `a_p <= v_q` for every ordered flag `(p,q)`.
5. `a_q <= bottom` for every bad q.

`models_iff_laws` proves that satisfying the actual generated list is equivalent
to these clause families; the proof does not assume an abstract unverified
encoding interface. The list is grouped by source state rather than by clause
family. This ordering difference does not change the constraint system.

## Source and direct proof structure

### TerminalRealization.lean

Imports only `Subtail.TreeSemantics`, which imports `Subtail.Basic`.

`nonfinal_of_nonempty_run` proves that a control with a defined nonempty run
cannot be accepting. `upper_run` transports upper-copy membership down any
prefix and rejects missing transitions through the denied b. `lower_run`
transports lower-copy nodes up defined runs using the available lower clauses.

`separation_implies_witness` then proves every original `Basic.Witness`
conjunct: safety at all prefixes including zero, endpoint acceptance, and
unflaggedness for each ordered suffix-prefix agreement including diagonal
and empty-suffix cases. A prohibited `(p,q)` comparison uses `a_p <= v_q`,
not its converse.

For satisfiability, `baseNodes I q u` means that the run from q on u is defined
and ends at a nonaccepting control. Terminality proves prefix closure.
`baseline_models` assigns bottom to all a variables and b, and this explicit
possibly infinite tree to each v variable. `realization_satisfiable` packages
that valuation. No finite-tree or finite-depth substitute is used.

### TerminalRealizationModel.lean

Imports only the preceding module. It constructs the candidate-word model:

```text
A_q(t) := exists x,z, w = x ++ t ++ z and run(initial,x) = q.
V_q(t) := R_q(t)
          or exists x,y,r,p,
             t = x ++ y and run(q,x) = r and G(p,r) and A_p(y).
```

Thus A contains all prefixes of suffixes at occurrences of q, and V contains
forced lower roots and all propagated ordered flag seeds. `cut_append` makes
the prefix-closure split explicit: a cut strictly inside x reaches a forced
nonaccepting root, while a cut after x leaves a prefix of the upper seed.

`wordModel_models` verifies every generated clause when w is a Witness.
`wordModel_left` gives the unchanged query address in the upper tree.
`wordModel_right` excludes it from the lower tree: a baseline node contradicts
final acceptance, and a transported flag seed gives an original prohibited
ordered suffix comparison. The position order follows from the two exact
word decompositions and their lengths; no orientation or index transfer is
left unproved.

`witness_iff_separating` combines the two directions. The non-entailment
corollary invokes exactly `TreeSemantics.not_entails_iff_separating` with
`C = constraints I`, `a = a I.initial`, and `b = v I.initial`, then applies
the proved same-word equivalence. This is the elementary original semantic
existential-address theorem, **not** the forward summary bridge.

### TerminalRealizationAudit.lean

Imports the model module and checks both statement readback and small fixtures.
The fixture proofs use kernel reduction (`decide`), not `native_decide`.

Checked fixtures include an empty positive word, nonaccepting terminal rejection,
a bad initial state, a diagonal flag, reversal of a single ordered flag,
undefined transitions, actual separating/nonseparating model conclusions, and
two literal generated clause lists (including b's index and flag orientation).

The two-state `spine` instance loops on 0 and exits on 1 to a terminal final.
Besides its concrete witness and satisfiability, `spine_forced` proves that
**every model** contains the product address `0^N` in v_0 for every N.
`spine_unbounded` explicitly gives an address longer than each supplied bound.
Together with `spine_satisfiable`, this confirms nonvacuously that infinite
lower-copy trees are sometimes required, not just permitted by the definitions.

## Validation actually executed

The local container has no Lean/Lake installation and its direct network DNS
was unavailable. Lean verification was therefore executed remotely, in the
new read-only GitHub Actions workflow, and its completed logs were read back.
It was not inferred from source inspection or from another worker's build.

Environment reported by the successful job:

- Ubuntu 24.04.5, Linux x86_64.
- Lean 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
- The repository toolchain file was unchanged.
- Python 3.12.3 for the remote regression replay; seed 2026091930.
- Workflow timeout: 15 minutes. Python per-suite timeout: 120 seconds.
  No explicit memory ceiling was set.

Executed commands:

```sh
cd lean
lake build +Subtail.TerminalRealizationAudit
lake env leanchecker Subtail.TerminalRealization
lake env leanchecker Subtail.TerminalRealizationModel
lake env leanchecker Subtail.TerminalRealizationAudit
cd ..
PYTHONDONTWRITEBYTECODE=1 python3 experiments/replay_c030_independent.py \
  --output /tmp/c030-replay.json
```

The build compiled all three new modules successfully (six total build jobs
including dependencies). All three explicit kernel replay commands passed.
The workflow additionally generates an audit of **every named def/theorem in
all three files**, including simp-decorated declarations, and checks that the
72 requested names exactly match the 72 returned transitive axiom readbacks.
It fails on missing results or any axiom outside the permitted standard Lean
foundations, and separately rejects `Classical.choice` in the seven executable
variable/clause constructor declarations.

| Declaration or check | Actual result |
|---|---|
| `constraints` and its constructor dependencies | PASS; `propext`, `Quot.sound`; no choice |
| `realization_satisfiable` | PASS; `propext`, `Quot.sound` |
| `witness_iff_separating` | PASS; `propext`, `Quot.sound` |
| `not_entails_iff_witness` | PASS; also `Classical.choice`, inherited from the original semantic existential theorem |
| All 72 named declaration dependency closures | PASS; no custom axiom, `sorryAx`, or native evaluation axiom |
| All three independent kernel replays | PASS |
| 200196 word/model comparisons, 12956 baseline models, 416 positive words | PASS; archived semantic fields match |
| Separate finite-set countermodel after dropping terminality | PASS; explicitly outside the theorem's hypotheses |

Checked source SHA256 values, emitted by the actual audit job:

```text
TerminalRealization.lean
7ab0df63e8deb4ec4d9448298cee34cca74548e6578cb3994bbe204c3a56c429
TerminalRealizationModel.lean
aecfb3159e0d110acc57792370a600f90b945b224eeb74bb80102928020297f0
TerminalRealizationAudit.lean
064fa8410b668e94df2e6741632f34f69dbcec6ed179b4070db2faf4461d935d
```

The same independent checker was also replayed locally before merging PR #46;
all four suites and all eight archived artifact hashes matched. The remote
replay is an additional execution, not a second independent implementation.
The unchanged Python wrapper's own `not_run` field includes Lean: that wrapper
does not launch Lean. The separate preceding workflow steps above DID execute
and pass Lean compilation and kernel replay. Preserve this provenance rather
than rewriting the older wrapper's historical scope.

**Not established by these checks:** verification of the old production Python
bridge/realizer, a new E021 or budget differential replay, native evaluation
of the full subtype decider, or a second blind review of this Lean code.
The bounded Python corpus is not the proof of the all-input statement; the
Lean theorem supplies that statement independently.

## Failed attempts preserved in the branch history

The initial foundation build failed on conjunction association when unpacking
the list and a dependent `cases` equation already substituted into its goal.
These were corrected with `and_assoc` and reflexivity, respectively.
The next build compiled the foundation but exposed analogous dependent-case
proof terms, list/natural-number associativity simplifications and one redundant
tactic in the explicit model file. The completed model subsequently compiled.
The next audit build failed only because the terminality definition had to be
unfolded before deciding three closed fixture hypotheses. After that fix,
checkpoint `44725541...` passed every step above.

No target was weakened, semantics changed, extra assumption added, toolchain
changed, or placeholder/custom axiom introduced to obtain these results.
Intermediate failures and any superseded/cancelled workflow runs are historical
attempts, not successful verification of their snapshots. No history was forced
or erased.

## Integration boundaries and proposed canonical-record wording

Exactly five additive paths are owned by this contribution: the three Lean
files, this note, and `.github/workflows/lean-c030.yml`. The original proof,
Python artifacts, existing Lean files, shared CI, toolchain and ledgers are
unchanged. The shared `lean/Subtail.lean` aggregator is deliberately unchanged;
these are opt-in modules explicitly built by the dedicated workflow. Do not
infer their inclusion in the default import graph from a general Lake build.

The isolated workflow validates this branch and relevant PR changes. Before
retiring it or consolidating validation, the integrator should explicitly add
the modules and dependency audit to the shared build/kernel/CI path and ensure
future Basic/TreeSemantics changes retrigger the check. That shared-path change
is not part of this new-file contribution and requires current ownership
coordination. A new PR's repository-wide checks are separate from the pinned
successful run above and must be reported at their actual status.

Suggested C030 ledger addition, subject to the serialized integrator:

> The satisfiability and same-word realization core is separately Lean-checked
> in `TerminalRealization`/`TerminalRealizationModel`, using exactly 2k+1 indexed
> variables and only terminal-finality. Direct tree-model proofs do not use the
> forward bridge. See the certification note and pinned kernel/audit evidence.
> The broader ledger's budget-preservation subclaim retains its written-proof
> and experimental status; this entry does not promote it to LEAN.

The historical terminal-realization note and E021 entry can link to this note
and the original independent review without relabelling old experiment results.
C029 completion and finite-expression normalization have separate active owners;
this work does not duplicate, replace or reserve their modules. Requests for
shared navigation updates were posted to #37; no acknowledgment is assumed.

The PR #46 merge lease is released. The final contribution handoff in #37
records the new PR, actual source and documentation checkpoints, and releases
all certification paths. No continuing worker or background activity is implied.
A successor must inspect current main, the PR head and current ownership before
integrating or changing interfaces. Completing this converse certification does
not make it a dependency of the forward decision procedure and does not decide
Problem 1.7 or establish a complexity equivalence.
