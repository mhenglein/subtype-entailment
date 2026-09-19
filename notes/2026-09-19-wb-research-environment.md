# wb-marcus research environment

Date: 2026-09-19. Owner-authorized operational setup, coordinated in
[#37](https://github.com/mhenglein/subtail/issues/37#issuecomment-5738426072).
This continues the earlier [tooling investigation](2026-09-19-agent-tooling.md).
No mathematical investigation or unattended research job was started.

## Host and checkout

| Item | Verified configuration |
|---|---|
| SSH host / user | `wb-marcus` / `marcus` |
| OS / architecture | Ubuntu 26.04 LTS / Linux aarch64, systemd-nspawn container |
| Capacity | 8 CPUs, about 30.9 GiB RAM, about 91 GiB free after setup |
| Repository | `/home/marcus/workspaces/subtail`, private `mhenglein/subtail` |
| Worker directory | `/home/marcus/workspaces/subtail-worktrees` |
| Runtime and logs | `/home/marcus/.local/share/subtail` |
| Shell environment | `/home/marcus/.local/share/subtail/env.sh` |
| Lean | 4.33.1, commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` |
| elan / uv | 4.2.4 / 0.12.17 |
| Project Python | 3.13.14 in the checkout's `.venv`; system Python unchanged |
| GitHub CLI | 2.46.0 from Ubuntu packages |
| Codex CLI | Existing 0.147.0 installation and ChatGPT login |
| Lean MCP | lean-lsp-mcp 0.30.0, leanclient 0.13.2, mcp 2.0.0 |

The checkout was initially seeded from an exact Git bundle at
`0f1c88424cedd83874856c7e344442a88dd03bea`, while GitHub authorization was
pending. Only committed repository content was transferred. Both temporary
bundle copies were removed. After authentication, an actual GitHub fetch
succeeded and `main` was configured to track `origin/main`.

During setup, the coverage author integrated
`69f3be2f172bb9739bb22b78251e75f4bde3e704`. Both setup and remote checkouts
were advanced by fast-forward; its scientific changes were preserved. The
checks below identify the exact revision used, rather than treating results
from the initial checkout as results for this newer tree.

## Start a session

```sh
ssh wb-marcus
source /home/marcus/.local/share/subtail/env.sh
cd /home/marcus/workspaces/subtail
git status --short
git fetch origin main
```

Read current `AGENTS.md` and the owning issue before changing anything. The
canonical checkout is ready, but it is not a shared concurrent build area.
Create an owned branch and separate worktree for each worker after claiming
its scope. Keep each worktree's `.lake` outputs separate. Python's project
environment can be reused for the repository's standard-library experiments.

The installed `tmux` supports jobs that survive SSH disconnection. A detached
one-off setup validation was exercised successfully. No research service,
schedule, GitHub runner, or active research job was configured. An arbitrary
host reboot or reprovision is a separate persistence question below.

## Reproduce the runtime installation

Install the system prerequisites on a new Ubuntu ARM64 host:

```sh
sudo apt-get update
sudo apt-get install -y curl tar xz-utils zstd gh tzdata
```

Configure the intended host timezone and verify `/etc/localtime` is readable.
Then run [setup_research_host.sh](../scripts/setup_research_host.sh) as the
research user. It installs the pinned Lean and Python versions, uses pinned
elan/uv release assets with SHA-256 checks, and sets elan's default to the
repository's Lean version. It does not authenticate, clone, edit shell
profiles, or launch jobs. An existing elan installation is reused.
The final script passed `bash -n` and a second execution on the prepared host;
it reused the installed runtimes successfully.

The observed host already had tzdata 2026c, but had no `/etc/localtime`.
`timedatectl` reported UTC. Creating the missing link to
`/usr/share/zoneinfo/Etc/UTC` preserved that timezone and fixed the Lean language
server. Batch Lean builds had passed before the repair, while `lake serve --`
exited with `Watchdog error: no such file or directory`, naming
`/etc/localtime`. The bootstrap now checks this prerequisite before installing.

The installed uv executable is
`/home/marcus/.local/share/subtail/tools/uv-0.12.17/uv`.
To create the environments after an authenticated clone:

```sh
uv venv --python 3.13.14 .venv
uv venv --python 3.13.14 ~/.local/share/subtail/lean-lsp-mcp-0.30.0
uv pip sync --python ~/.local/share/subtail/lean-lsp-mcp-0.30.0/bin/python \
  scripts/lean-mcp-requirements.txt
```

These commands assume uv is on PATH. The installed `env.sh` provides the
project Python, elan and uv paths; no shell profile was changed. All 43 MCP
dependency versions match [the package list](../scripts/lean-mcp-requirements.txt),
and `uv pip check` passed. Package versions are pinned; this is not a
hash-locked Python dependency installation.

## GitHub and Codex access

Marcus authorized the existing GitHub CLI grant through GitHub's normal
device flow on this host. The stalled passkey check was completed using his
authenticator. No laptop GitHub token was copied.

Readback verified user `mhenglein`, the exact private repository, pull/push
permissions, an authenticated fetch, and issue #37 API access. `gh auth
setup-git` configured HTTPS Git authentication. No dummy branch was pushed.

This host has no available GitHub credential store. The CLI's credential file
is `/home/marcus/.config/gh/hosts.yml` with mode `0600`; its directory is `0700`.
No credential values are included in this note, repository or validation logs.
The user approved the existing CLI grant; it is broader than a repository-only
deploy key.

Remote Codex has enabled server `lean-lsp` in its user configuration. The
command is the dedicated environment's `bin/lean-lsp-mcp`, using local stdio
and default project `/home/marcus/workspaces/subtail/lean`. Settings match the
Mac pilot: 30-second startup allowance, 120-second tool allowance, explicit
elan PATH, `LEAN_BUILD_CONCURRENCY=share`, and five external search tools
disabled. Other Codex settings were preserved.

The configured server passed a real MCP protocol test with 18 local tools.
New remote Codex sessions can load the configuration. No existing task was
moved, and activation inside a new remote Codex agent session was not tested.
For another worktree, call a file-based tool with its absolute file path before
using a pathless code trial. The server setting is not a cross-agent build lock.

## Validation evidence

Logs are under `/home/marcus/.local/share/subtail/logs`.

At initial revision `0f1c88424cedd83874856c7e344442a88dd03bea`:

- PASS: index/link validation and all 13 navigation tests.
- PASS: `python experiments/run_experiments.py`.
- PASS: `python scripts/check_lean.py`: default Lake build, `Subtail` kernel
  replay, core axiom audit and finite Python/Lean differential regressions.
- PASS: additional `Subtail.RankQueryUnwind` kernel replay.
- Initial MCP check FAILED because `/etc/localtime` was missing. This is
  retained in `validation-2026-09-19.log` and its exit file; that run is not
  relabelled as a pass.
- After the host fix, PASS:
  [lean_mcp_smoke.py](../scripts/lean_mcp_smoke.py), recorded in
  `lean-mcp-pilot-fixed-2026-09-19.json`. It read a goal and diagnostics,
  accepted two valid proof trials, rejected an invalid trial, preserved the
  fixture, checked theorem axioms and standalone code, and kernel-replayed
  `Subtail.TwoState`.

At current base `69f3be2f172bb9739bb22b78251e75f4bde3e704`, the fresh remote
validation also PASSED:

- `python scripts/research_index.py --check` and all 13 navigation tests.
- `python scripts/check_lean.py`: default build including the newly integrated
  modules, `Subtail` kernel replay, core axiom audit and differential checks.
- Explicit kernel replays for `Subtail.RankQueryUnwind`,
  `Subtail.RankQueryEnumerationAudit` and `Subtail.RankQueryCoverage`.
- The complete MCP smoke described above, with the expected 18 local tools.
- The checkout remained clean; the saved Lean regression result was unchanged.

Evidence: `validation-69f3be2.log`, `validation-69f3be2.exit` (value `0`),
`lean-checks-69f3be2.log`, and `lean-mcp-pilot-69f3be2.json`. The one-off tmux
session ended. The standard-library experiment suite did not change between
the two checked revisions and was not repeated. The added enumeration census
and every per-module axiom audit were not rerun separately on this host;
the existing [main Lean CI run](https://github.com/mhenglein/subtail/actions/runs/35415095361)
was independently read back as successful on exact revision `69f3be2`.

These are environment and regression checks, not independent mathematical
review or a claim that the subtype entailment problem is solved. Full workflow
audits and larger research searches are separate from this provisioning scope.

## Storage persistence still needs a provider check

The checkout and runtime directories are on `/`, an ext4 filesystem on
`/dev/nvme3n1`. The host reports Amazon Elastic Block Store disks. This does
not establish whether the workbench retains that volume when the host is
reprovisioned or deleted. The available local Kubernetes client has no current
context, so no volume or provider retention policy was read back. No reboot,
reprovision or storage change was attempted.

Treat committed and pushed GitHub content as durable. The host is ready for
CPU work and disconnect-surviving sessions, but unique uncommitted results,
logs and caches must not be assumed to survive reprovisioning. The remaining
infrastructure question is the workbench's volume retention/backup policy.
No new backup destination or schedule was configured.
