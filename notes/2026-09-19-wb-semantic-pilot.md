# Workbench proof pilot: semantic promotion without a weight bound

Date: 2026-09-19. Workstream A018, claim C080, issue #30; coordination #37.
Base: `8d23842a1d7ccbd620484563a982b7b779aa0d82`.
Branch: `codex/wb-semantic-pilot-20260919`.
Scope: one small proof obligation and an actual remote Lean-tool workflow.

## Exact result

[RankQuerySemanticUnwind.lean](../lean/Subtail/RankQuerySemanticUnwind.lean)
proves, for every query, natural promotion budget h and safe base reference B:

```text
Sat(P(B), promote pre phi h)
iff there exist n <= h and C such that
    Promotes I n B C and Sat(P(C), phi).
```

The generic theorem requires only semantic closure for every query and safe
reference. It retains all original quantifiers and safety hypotheses. Its
induction is adapted from the existing `RankQueryUnwind.sat_promote_iff`, whose
proof used only the semantic half of the bundled `ClosureFor` contract.
The concrete `sat_promote_preimage_iff` supplies that hypothesis using
`RankQueryCoverage.closure_iff` for the existing finite `preimage I budget`.
Neither theorem assumes a query-weight bound, `ClosureFor`, F(k), terminality,
a witness bound or a decision oracle. The generic theorem does assume the
explicit semantic equivalence; the concrete theorem discharges it.

This does **not** prove `RankDecisionStatement`, finishing correctness, F(k),
Q004 or the arbitrary-tree subtype decision. It isolates a sufficient semantic
dependency for the direct algorithm already proposed in
[Section 8 of the candidate outline](2026-09-15-candidate-rank-query-decision.md).
There are no new runtime definitions in this module.

## Independent statement readback

A separate read-only agent, `semantic_pilot_review`, inspected the actual remote
source and the imported definitions at the base above. It checked the source
hash `2b3968f40f9b42d9bc051a0d6b11de3c80e2c3bd30351b04f579765960c9b3de`.
It found no dropped safety hypothesis, circular use of the weighted theorem,
or use of the numerical bound. It read the parent's context, so this was a
separate source review, not a blind derivation. It did not run Lean or
independently recertify the imported coverage theorem. The parent performed
the build, MCP tests and kernel replay separately.

## Remote tooling exercised

Host: `wb-marcus`, Ubuntu ARM64; Lean 4.33.1; Python 3.13.14;
lean-lsp-mcp 0.30.0, leanclient 0.13.2, mcp 2.0.0.
Worktree: `/home/marcus/workspaces/subtail-worktrees/wb-semantic-pilot-20260919`.
The original main checkout and its Lake output were not used as a shared build.

The [reproducible MCP pilot](../scripts/lean_semantic_pilot.py) used the host's
configured stdio server, with its unchanged default project pointing at main.
An absolute file call selected the new worktree. The subsequent pathless code
trial read a unique relative marker created only under that worktree's `.lake`.
The correct marker passed; a deliberately incorrect value failed. The marker
was then removed. This check remains discriminating after the module also
exists on main. The initial import-only probe passed too, but was strengthened
before publication because it would become ambiguous after integration.

- PASS: pinned runtime, authenticated GitHub identity/read and clean base.
- PASS: fresh target build including 17 build jobs, 30.224 seconds.
- PASS: 18 local MCP tools exposed; no external proof-search service.
- PASS: complete clear diagnostics and the actual concrete promotion goal.
- PASS: two valid tactic trials accepted; one invalid tactic rejected.
- PASS: source unchanged by proof trials; both theorem axiom checks allow only
  the repository's standard axioms; no unfinished proof or custom axiom.
- PASS: target kernel replay, 1.067 seconds; warm target build,
  0.166 seconds.
- PASS: isolated-worktree selection for the pathless code trial, wrong-marker
  negative control, and removal of the temporary marker.
- PASS: the Mac session's native Lean goal tool read a current proof goal too.

Remote call times: diagnostics 1.145s, goal 0.021s,
three tactic trials 1.808s, standalone code 0.938s,
wrong-marker check 0.023s, and theorem checks
1.585s/0.050s. These are one pilot's
measurements, not general throughput guarantees.

Exact source/script hashes, goals, axioms, package versions and timings are
in [the machine-readable result](../results/wb-semantic-pilot.json).
Its `additional_checks` field is separate parent-recorded evidence for the
fresh build, host/GitHub preflight, detached combined check and Mac-native call.
Running the pilot script alone reproduces the MCP/kernel portion, not those
separate operational observations. Fresh-build jobs and timing come from the
saved first-build log/record; the script's `target_build_seconds` is the later
warm invocation. Build logs and raw MCP output remain in the worktree's ignored
`tmp/wb-semantic-pilot/` directory. The source and result are preserved in Git.
The pinned toolchain and configuration were reused; no credential was copied.

## Reproduction

From an isolated checkout on the prepared workbench:

```sh
source /home/marcus/.local/share/subtail/env.sh
/home/marcus/.local/share/subtail/lean-lsp-mcp-0.30.0/bin/python \
  scripts/lean_semantic_pilot.py --output /tmp/semantic-pilot.json
python scripts/check_lean.py
python scripts/research_index.py --check
```

The output records the current base revision and exact source hashes. The
stored result was captured on an uncommitted combined tree above the named
base, with the default import present. Its exact module and script hashes are
recorded; do not relabel it as a fresh run on a later commit.

## Remaining proof task and limits

The next discriminating task is the exact terminal decision schema:
`TerminalFinals I -> RankDecisionStatement I (preimage I budget)`.
It needs the released finishing interface, safe milestone-chain coverage,
reverse reconstruction, executable one-letter safety, and empty/small-state
cases. The numerical weight/F(k) result remains separate. After terminal
BorderAvoid, the effective subtype reduction still needs completion and
statement review for arbitrary, possibly infinite trees.

Native tool activation inside a newly created remote Codex task was not tested:
this pilot used the real remote MCP protocol from the current task over SSH.
No reboot, host reprovisioning, long-duration load or volume-retention policy
was tested. The configured tools' presence is not a performance test of every
one of the 18 endpoints. No broad autonomous research job was launched.


## Combined-tree validation and disconnect survival

The new module was added to the default `Subtail` import graph before these
checks. A named tmux job on wb-marcus ran the checks after the initiating SSH
connection closed; a separate SSH connection observed it still running, and
later read its completed result. This proves survival of that connection loss,
not survival of host restart or reprovisioning.

- PASS: `python scripts/check_lean.py` (105.239s).
- PASS: `python scripts/research_index.py --check` (0.315s).
- PASS: `python -m unittest discover -s scripts -p test_research_index.py` (0.165s).
- PASS: `git diff --check` (0.016s).

`check_lean.py` includes the default build, kernel replay, core axiom checks
and finite Python/Lean differential regressions. All 13 navigation tests
passed. The regenerated `results/lean-checks.json` was byte-identical to main.
No existing proof module, theorem signature, runtime, toolchain or workflow
was changed; the only existing Lean edit is the new default import. Inherited
coverage-module linter warnings are unchanged. The two new declarations had
complete clear diagnostics and their own axiom/kernel checks in the pilot.

The strengthened marker test was rerun successfully after the combined check;
Lean source was unchanged. Final documentation edits require only index and
diff checks. The complete source contribution and exact published revision
are recorded in the #30/#37 integration handoff. No background research or
validation job remains after completion.


## Provisioning gap found and repaired

The first commit attempt failed with `Author identity unknown` (exit 128).
GitHub authentication and fetch access did not establish that Git could author
a commit. The staged contribution remained intact. Set this repository's local
`user.name` and `user.email` from the existing Mac Subtail identity, then
`git var GIT_AUTHOR_IDENT` passed. No credential was copied and global Git
settings were not changed. New worktrees of this repository inherit the local
identity. Future host preparation should test commit identity separately from
GitHub authentication. The initial failure is retained in the result rather
than relabelled as a successful first attempt; actual commit/push readback is
in the integration handoff.
