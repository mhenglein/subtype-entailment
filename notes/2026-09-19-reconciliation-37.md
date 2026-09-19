# Repository reconciliation #37: inspected checkpoint and branch disposition

Date: 2026-09-19 UTC (September 18 in New York).
Actor: ChatGPT reconciliation integrator, authorized by the repository owner.
Coordination: [#37](https://github.com/mhenglein/subtail/issues/37).
Operational change: [#38](https://github.com/mhenglein/subtail/pull/38).

This is a dated operational inventory, not a second scientific claims ledger.
The canonical scientific status remains in STATE.md, the claims/approach
records and [#34](https://github.com/mhenglein/subtail/issues/34). No accepted
proof, query definition, experiment implementation, toolchain, import aggregator
or scientific status is changed by this operational patch.

## Scope and actual access

The inspected starting main is
`a4e9dfcdcf41abf9c14f4e7c2977e9cb530b5c74`.
All ahead/behind counts below are relative to that immutable starting point,
not a promise that they remain current after later integrations. Exact remote
heads, per-file comparisons and recent task comments were read through GitHub.
The final published main revision and actual check results belong in the
completion comment on #37; they must be read, not inferred from this report.

No pre-existing Subtail checkout was present in the inspected local runtime
locations. Git and filesystem inspection did not establish access to any other
agent's workspace. A normal remote Git read failed because github.com could not
be resolved in that runtime; the authorized GitHub connector remained usable.
No local Lean installation or full repository test execution is claimed.
Remote CI is the validation channel for this patch.

Unpushed commits, staged/unstaged files, untracked files, stashes and other
agents' worktrees are NOT visible in GitHub's branch inventory. Their status is
**not inspected**, not "clean". No such work was reset, cleaned, committed or
deleted by this session. Workers were asked for explicit checkpoint reports.

## Seven research branches at the starting inventory

All seven names below have prefix `lean/` and suffix `-2026-09-18`.
The file counts are actual branch-side changes from the common ancestor; they
are not a proof that all content is semantically unique relative to main.

| Branch | Exact inspected HEAD | Ahead / behind | Added paths | Disposition for this pass |
| --- | --- | --- | --- | --- |
| closure-reconstruction | `10f1c9892a6fd24f37c9d754a4e04cee5fc15d1a` | 10 / 45 | 4 | Preserve. Its target overlaps the delivered reverse theorem; no blanket merge or deletion. Request an owner decision on unique reusable work versus an archived alternative. |
| diagram-enumeration | `35fcd103fcc0d89588524f5cec1f0e77ab67f108` | 6 / 1 | 6 | Source contribution delivered/released, but a newer coverage-worker claim reserves its integration. Defer overlapping integration until explicit coordination. |
| global-marks | `da032fc89da5f54a825b8114dac659d41ee96ebb` | 3 / 19 | 2 | Preserve the active stage-4b support claim; do not infer release from inactivity or a later task elsewhere. |
| run-transport-support | `8d6b9522b69e2fddcdff9cda12d22c45910826be` | 5 / 26 | 2 | Preserve pending disposition: one comment calls it superseded/do-not-merge, a later one reports the repaired result again. |
| portal-transport-support | `7d5c6b3cd81aa9f77f741e3dc5d684b857d4daa8` | 2 / 25 | 2 | Preserve as delivered independent support pending owner disposition; main's reverse-proof author reports equivalent lemmas already in RankQuerySound. |
| finish-query-support | `8d479c2021477beef178b641bb379d4bea5acf32` | 1 / 0 | 1 | Do not integrate this draft. Its bare-Step source-permission claim is false at the stated arbitrary-Graph scope; ask the owner to reconcile with the Facts branch. |
| finish-query-facts | `25b329b464906e7cc034bd3149222a99962ce0c7` | 2 / 0 | 2 | Candidate repair of the finishing helpers; preserve the active worker's scope and require an explicit authoritative-branch handoff and exact checks. |

Actual changed paths inspected through comparisons:

- Reconstruction: `RankQueryReconstruction.lean`,
  `RankQueryReconstructionFamily.lean`,
  `RankQueryReconstructionGenerator.lean`, and
  `.github/workflows/lean-closure-reconstruction.yml`.
- Enumeration: `RankQueryEnumeration.lean`, `RankQueryEnumerationAudit.lean`,
  `.github/workflows/lean-rank-enumeration.yml`,
  `experiments/check_rank_enumeration.py`,
  `notes/2026-09-18-rank-query-enumeration.md`, and
  `results/lean-rank-enumeration.json`.
- Marks: `RankQueryMarks.lean` and `.github/workflows/lean-global-marks.yml`.
- Run transport: `RankQueryRunTransport.lean` and
  `.github/workflows/lean-run-transport-support.yml`.
- Portal transport: `RankQueryPortalTransport.lean` and
  `.github/workflows/lean-portal-transport-support.yml`.
- Finishing draft: `RankQueryFinish.lean`.
- Finishing facts: `RankQueryFinishFacts.lean` and
  `.github/workflows/lean-finish-query-facts.yml`.

Lean module paths in this list are under `lean/Subtail/`.
No whole-tree semantic equivalence audit of every alternative module is claimed.

## A live claim not established by the initial remote-branch list

The coverage author's [00:31 UTC claim in #28](https://github.com/mhenglein/subtail/issues/28#issuecomment-5737860979)
names `lean/rank-query-coverage-2026-09-19`, new coverage/chain modules,
enumeration integration, shared imports, A018 and tracker updates. That branch
was not in the initial seven-branch snapshot. This does not establish that its
local work is absent or abandoned.

The earlier enumeration [delivery](https://github.com/mhenglein/subtail/issues/28#issuecomment-5736459709)
released its six source paths and requested integration, but the newer claim
already reserves that integration. This session therefore did NOT independently
merge the enumeration, modify its interfaces or take the shared aggregator and
ledger paths. A narrow handoff request was posted in
[#28](https://github.com/mhenglein/subtail/issues/28#issuecomment-5737944465).
The coverage proof itself remains with its worker.

Readback of the delivered enumeration confirms that `mem_diagrams` concerns an
independently defined finite syntax bound; `preimage_sound` inherits the reverse
construction; and `DiagramCoverage` remains an explicit unproved premise of the
forward and biconditional endpoints. The delivery records source-revision CI,
kernel and 51 named dependency audits, not a proof of forward coverage or a
fresh combined-tree validation by this reconciliation. No status is promoted.

## Why the finishing branches must not both be merged

At `8d479c2`, `RankQueryFinish.finish_step_facts` concludes that the SOURCE
vertex is not an end vertex from `Step` alone. At inspected main, `Step` is

    exists label, edge(source,label)=target
      and targetControl belongs to observer.move(...)
      and Allowed(target).

It does not require `Allowed(source)`. `finishObserver.move` ignores the source
colour. Its K transition checks the target's end flag, predecessor transition,
bad/diagonal flags and mask only.

A concrete counterexample to the extra source conclusion uses the existing
one-state `toy` instance, two graph vertices, source.isEnd=true,
target.isEnd=false, all masks false, and a K_false edge from source to target.
The sole control 0 passes the predecessor, flag and target permission checks.
Thus the Step premise holds but the extra source conclusion does not. This is
a direct semantic counterexample argument from the definitions, not a compiled
Lean counterexample fixture or a new claim about unrestricted entailment.

At `25b329b`, `RankQueryFinishFacts.finish_step_facts` removes that source
conclusion. Its `finish_run_notEnd` instead derives both endpoint permissions
from a Run. This is a candidate repair, not evidence that the entire finishing
query is correct. Both module headers explicitly exclude full finishQuery /
Witness equivalence. The issue-level finding and authoritative-branch request
are [in #30](https://github.com/mhenglein/subtail/issues/30#issuecomment-5737965530).

## Transport/reconstruction disposition requires owner reconciliation

The [15:01 UTC support handoff](https://github.com/mhenglein/subtail/issues/29#issuecomment-5731890012)
reports a checked portal helper and calls the run-transport branch superseded.
The [reverse-proof delivery](https://github.com/mhenglein/subtail/issues/29#issuecomment-5732218829)
says the portal helper was not imported because equivalent lemmas are in the
canonical module, and flags the reconstruction branch's overlapping target.
The later [00:22 UTC run-support report](https://github.com/mhenglein/subtail/issues/29#issuecomment-5737796876)
again describes the repaired run-transport result. The closed issue's initial
"Unclaimed" text is not the live ownership record.

The [reconciliation request](https://github.com/mhenglein/subtail/issues/29#issuecomment-5737970328)
asks owners to identify unique reusable results, replacements, consumers and
local-only work before integration or archival. A closed proof obligation does
not by itself release every supporting branch or prove it can be deleted.

## Changes authorized and made by this operational patch

AGENTS.md now requires current-main instruction recovery, explicit issue-first
ownership and interface agreements, a single integration lease that respects
pre-existing reservations, pushed handoff SHAs and local-only-work reports,
combined-tree checks, and safe branch retirement. The blanket worker permission
to push scientific updates directly to main is removed. Scientific evidence
classes, exact semantics, independent checking, failed-attempt preservation and
conditional-result warnings are retained.

These are documented operating rules. This patch does not claim that server-side
branch protection has been enabled or that all active agents have acknowledged
the messages. Posting a request is not the same as receiving a handoff.

No existing research branch, tag or shared history is rewritten or deleted by
this patch. No proof module, workflow, toolchain or canonical claim is changed.
The inventory is intentionally useful without pretending that all working
copies are visible or that every latest draft belongs on main.

## Completion criteria and remaining work

Before publishing, inspect this PR's actual diff and exact-revision checks,
re-read main/ownership, and reject a conflicting or unvalidated integration.
After publication, record the resulting SHA and check status in #37 and release
this session's lease. The note's creation is not itself a passing test result.

Remaining work is explicitly bounded: resolve the enumeration integration
handoff; identify the authoritative finishing branch; reconcile support-branch
dispositions; obtain relevant workers' local-work checkpoint reports; then
validate and integrate coherent scientific increments. Keep #37 open for these
follow-ups rather than claiming the full reconciliation is complete. C080 and
its still-open proof obligations remain unchanged.
