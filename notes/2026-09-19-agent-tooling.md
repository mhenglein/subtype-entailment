# Agent tooling setup and remote-host investigation

Date: 2026-09-19. Owner authorization and path scope:
[#37](https://github.com/mhenglein/subtail/issues/37#issuecomment-5738226482).
Base: `5e156fc67b3516c9c3955f41b2cc7940dccfd210`.
This is operational work. Mathematical research remains paused and C080's
status is unchanged.

## Actions and the original source request

Marcus reports the Actions billing/access issue fixed and is investigating
cheaper alternatives himself. New runs were executing successfully during this
session, including [35412487327](https://github.com/mhenglein/subtail/actions/runs/35412487327).
No alternative CI service or runner was configured, and no unrelated workflow
was rerun as a billing test.

Marcus also instructed us to assume `analysis-2026` will not arrive and to
stop requesting it. [A007](../research/approaches/A007.md) is now `retired`,
not blocked or tried. Its scientific outcome stays open: the original census
has not been reproduced. Issue #1 is closed as not planned. The source PDF,
historical review and independent implementation remain unchanged.

## Local Lean MCP installation

Installed [lean-lsp-mcp](https://github.com/oOo0oOo/lean-lsp-mcp) **0.30.0**
from PyPI in a dedicated Python 3.13.14 virtual environment:

`/Users/marcushenglein/.local/share/subtail/lean-lsp-mcp-0.30.0`

The complete installed dependency versions are in
[lean-mcp-requirements.txt](../scripts/lean-mcp-requirements.txt).
`pip check` passed. The existing Lean 4.33.1 / Lake installation is reused;
no Lean package or proof source was changed.

Registered user-scoped Codex MCP server `lean-lsp` using `codex mcp add`.
`codex mcp get lean-lsp --json` confirms it is enabled, uses the installed
absolute executable, and communicates locally over stdio. Its default project
is the root checkout's `lean/` directory. Absolute file paths select the correct
Lean project in another worktree; the pilot exercised that switch explicitly.
Call a file-based tool on the intended worktree before a pathless code trial.

Settings: 30-second server startup allowance, 120-second tool allowance,
`LEAN_BUILD_CONCURRENCY=share`, and an explicit PATH containing the existing
Lean binaries. Five external search tools are disabled; the 18 local proof,
navigation and analysis tools are available. No network listener or remote
Lean service was started. The optional REPL/Mathlib/Loogle installs were not
needed for this pilot. Separate agents still need separate worktrees and
coordination around builds; the server's build setting is not a cross-process
or cross-agent lock.

The current conversation's advertised tools do not refresh from this config
change. Restart Codex to load the integration. Configuration readback and a real
MCP client were tested here; an actual post-restart Codex tool call remains the
client-side activation check.

## Executed compatibility pilot

[Smoke script](../scripts/lean_mcp_smoke.py),
[recorded result](../results/lean-mcp-pilot.json).

```sh
~/.local/share/subtail/lean-lsp-mcp-0.30.0/bin/python \
  scripts/lean_mcp_smoke.py --output /tmp/subtail-lean-mcp.json
```

Run from a checkout with the configured server and its Python environment.
The script builds only the existing `Subtail.TwoState` dependency slice and
creates a temporary Lean file below `.lake`. It removes that file on exit.
The recorded run used the isolated tooling worktree, not another worker's
build directory.

Actual results with Lean 4.33.1:

- MCP initialization and the configured 18-tool listing passed.
- A file importing `Subtail.TwoState` elaborated with no diagnostics.
- The goal reader returned `n : Nat; ⊢ n = n` before `rfl`, and no goals after.
- Isolated `rfl` and `simp` trials passed. An invalid proof of `False` returned
  an error. The original file remained unchanged. Empty remaining goals alone
  are not treated as success when diagnostics contain an error.
- The small identity theorem had no axioms. The existing two-state correctness
  theorem reported only `propext` and `Quot.sound`.
- A standalone code trial importing the repository passed.
- `lake env leanchecker Subtail.TwoState` passed.

The initial probe needed a client-side field-name correction for MCP Python
SDK 2 (`model_dump(by_alias=True)` supplies the protocol's names). The final
script and recorded result include that correction. These checks establish
tool compatibility on this slice, not a full repository proof replay or a new
mathematical result. Large in-progress proof modules were not benchmarked.

## wb-marcus: investigated, not provisioned

An independent read-only worker inspected the configured SSH host. Root
rechecked CPU, memory, disk, workspace access and tool availability with
`ssh -o BatchMode=yes -o ConnectTimeout=10 -o StrictHostKeyChecking=yes wb-marcus`.

| Property | Observed |
|---|---|
| System | Ubuntu 26.04 LTS, ARM64 |
| CPU | 8 cores |
| RAM | 32,441,828 kB, about 30.9 GiB; no swap |
| Free storage | About 93.4 GiB on the NVMe filesystem |
| Workspace | `/home/marcus/workspaces` exists and is writable |
| Installed | Python 3.14.4, Git, Codex CLI, tmux |
| Missing from PATH | Lean, Lake, elan, uv, GitHub CLI |
| GitHub Git access | Private-repository HTTPS access failed without credentials |

No Subtail checkout was found at the candidate workspace paths inspected;
this is not a complete disk census. Codex reported an existing ChatGPT login,
which does not establish GitHub repository access. No credentials were copied.
A GitHub SSH probe briefly added a host-key entry; the worker removed its own
entry and reported restoring the prior diagnostic-file state. No repository,
runtime, service or research job was installed or moved on the host.

The capacity is suitable for a first persistent CPU workspace. A later,
separately authorized bootstrap should configure repository access directly on
the host, install the pinned Lean toolchain and a reproducible Python
environment, clone Subtail, and verify the same pilot and kernel checks there.
Use separate worktrees with logs and explicit checkpoints. The ext4/NVMe and
42-day uptime observations do not establish persistence across workbench
reprovisioning; that retention policy still needs verification. GitHub remains
the durable source of committed research.

Marcus owns local disk cleanup. This session performed none.

## Repository validation

The tracker supports `retired` as an execution disposition without changing a
claim's scientific outcome. Regression tests verify that a retired record is
still retrievable, is absent from active/tried/blocked counts, and has no current
owner. Thirteen navigation/status tests, `research_index.py --check`, and
`git diff --check` passed. No proof obligation was reassigned or resumed.
