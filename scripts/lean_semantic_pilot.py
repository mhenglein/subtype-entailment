"""Exercise the configured Lean MCP server on the semantic-only unwind theorem.

Use the Lean MCP virtualenv's Python. This script reads the configured server,
selects an isolated worktree via an absolute file tool call, checks proof trials
without editing the source, and kernel-replays the target. The result records
source hashes because an uncommitted target is permitted during development.
"""

import argparse
import asyncio
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import subprocess
import time
import tempfile
import uuid

from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client

ROOT = Path(__file__).resolve().parents[1]
MODULE = "Subtail.RankQuerySemanticUnwind"
THEOREMS = ("sat_promote_iff", "sat_promote_preimage_iff")
STANDARD_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
EXTERNAL_SEARCH = {
    "lean_leansearch", "lean_loogle", "lean_leanfinder",
    "lean_state_search", "lean_hammer_premise",
}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def command(args, cwd, timeout=120):
    started = time.monotonic()
    result = subprocess.run(args, cwd=cwd, text=True, capture_output=True,
                            timeout=timeout, check=True)
    return result.stdout.strip(), round(time.monotonic() - started, 3)


async def exercise(configuration, project, source):
    transport = configuration["transport"]
    require(transport["type"] == "stdio", "Expected the configured stdio server")
    params = StdioServerParameters(
        command=transport["command"], args=transport.get("args", []),
        env={**os.environ, **(transport.get("env") or {})}, cwd=str(project.parent),
    )
    original = source.read_bytes()
    line, tactic = next((i, text.strip()) for i, text in
                        enumerate(original.decode().splitlines(), 1)
                        if text.startswith("  exact sat_promote_iff I"))
    timings = {}
    async with stdio_client(params) as (reader, writer):
        async with ClientSession(reader, writer, read_timeout_seconds=90) as session:
            initialized = (await session.initialize()).model_dump(by_alias=True)
            listed = (await session.list_tools()).model_dump(by_alias=True)
            names = {tool["name"] for tool in listed["tools"]}
            needed = {"lean_goal", "lean_diagnostic_messages", "lean_multi_attempt",
                      "lean_verify", "lean_run_code"}
            require(needed <= names, "Required proof tools are missing")
            require(not names & EXTERNAL_SEARCH, "Expected only local proof tools")

            async def call(name, arguments, label=None):
                started = time.monotonic()
                result = (await session.call_tool(name, arguments)).model_dump(by_alias=True)
                timings[label or name] = round(time.monotonic() - started, 3)
                require(not result.get("isError"), f"{name} returned an MCP error: {result}")
                value = result.get("structuredContent")
                require(isinstance(value, dict), f"{name} returned no structured result")
                return value.get("result", value)

            # A file-based call must select this worktree even when the
            # configured default project is a different checkout.
            diagnostics = await call("lean_diagnostic_messages", {
                "file_path": str(source), "timeout_s": 30,
            })
            require(diagnostics.get("success") and not diagnostics.get("partial"),
                    f"Incomplete/failed diagnostics: {diagnostics}")
            require(not diagnostics.get("items"), f"Unexpected diagnostics: {diagnostics}")
            goals = await call("lean_goal", {
                "file_path": str(source), "line": line, "timeout_s": 30,
            })
            require(any("Promotes" in str(goal) for goal in goals.get("goals_before", [])),
                    f"Did not read the actual promotion-chain goal: {goals}")
            require(goals.get("goals_after") == [], "Concrete proof did not close its goal")

            snippets = [tactic, "simpa using " + tactic.removeprefix("exact "),
                        "exact False.elim (by assumption)"]
            attempts = await call("lean_multi_attempt", {
                "file_path": str(source), "line": line, "snippets": snippets,
            })
            items = attempts.get("items", [])
            require(len(items) == 3, "A proof trial is missing")
            for item in items[:2]:
                require(not item.get("timed_out") and item.get("goals") == []
                        and not item.get("diagnostics"), f"Valid trial failed: {item}")
            require(any(d.get("severity") == "error" for d in items[2].get("diagnostics", [])),
                    "Invalid proof trial was not rejected")
            require(source.read_bytes() == original, "Proof trial modified the source")

            axioms = {}
            for theorem in THEOREMS:
                result = await call("lean_verify", {
                    "file_path": str(source), "theorem_name": f"{MODULE}.{theorem}",
                }, f"verify_{theorem}")
                require(set(result["axioms"]) <= STANDARD_AXIOMS,
                        f"Nonstandard axiom in {theorem}: {result}")
                axioms[theorem] = result["axioms"]
            # A unique relative marker remains discriminating after the new
            # module has also been integrated into the default main checkout.
            nonce = uuid.uuid4().hex
            with tempfile.NamedTemporaryFile(mode="w", prefix="semantic-pilot-",
                    suffix=".txt", dir=project / ".lake", delete=False) as handle:
                handle.write(nonce)
                marker = Path(handle.name)
            try:
                relative = json.dumps(marker.relative_to(project).as_posix())

                def marker_code(expected):
                    return (f"import {MODULE}\n#eval show IO Unit from do\n"
                            f"  let value ← IO.FS.readFile {relative}\n"
                            f"  unless value == {json.dumps(expected)} do\n"
                            '    throw (IO.userError "worktree marker mismatch")\n')

                standalone = await call("lean_run_code", {
                    "code": marker_code(nonce),
                })
                require(standalone.get("success") is True,
                        f"Pathless trial selected the wrong worktree: {standalone}")
                wrong_marker = await call("lean_run_code", {
                    "code": marker_code("wrong-" + nonce),
                }, "lean_run_code_negative_control")
                require(wrong_marker.get("success") is False,
                        "Incorrect worktree marker was not rejected")
            finally:
                marker.unlink(missing_ok=True)
            require(source.read_bytes() == original, "Source changed during the pilot")
            return {
                "server_version": initialized["serverInfo"]["version"],
                "local_tools_exposed": len(names),
                "diagnostics_complete_and_clear": True,
                "goal_before": goals["goals_before"], "goal_after": goals["goals_after"],
                "valid_trials": 2, "invalid_trials_rejected": 1,
                "source_unchanged": True, "axioms": axioms,
                "pathless_trial_selected_isolated_worktree": True,
                "wrong_worktree_marker_rejected": True,
                "worktree_marker_removed": not marker.exists(),
                "call_seconds": timings,
            }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=ROOT / "lean")
    parser.add_argument("--codex-server", default="lean-lsp")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    project = args.project.resolve()
    source = project / "Subtail/RankQuerySemanticUnwind.lean"
    configuration = json.loads(command([
        "codex", "mcp", "get", args.codex_server, "--json"], ROOT)[0])
    require(configuration["enabled"], "Configured Lean server is disabled")
    version = command(["lake", "env", "lean", "--version"], project)[0]
    require("version 4.33.1," in version, "Expected pinned Lean 4.33.1")
    build_output, build_seconds = command(["lake", "build", "+" + MODULE], project)
    checks = asyncio.run(exercise(configuration, project, source))
    _, replay_seconds = command(["lake", "env", "leanchecker", MODULE], project)
    result = {
        "status": "PASS", "scope": "Remote MCP and semantic-only promotion unwind; not a decision theorem",
        "lean_version": version, "base_revision": command(["git", "rev-parse", "HEAD"], project)[0],
        "module_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
        "pilot_script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "packages": {name: importlib.metadata.version(name)
                     for name in ("lean-lsp-mcp", "leanclient", "mcp")},
        "target_build_seconds": build_seconds,
        "kernel_replay": "PASS", "kernel_replay_seconds": replay_seconds,
        "checks": checks,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
