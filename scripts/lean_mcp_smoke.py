"""Exercise the configured Lean MCP server against the pinned repository core.

Run with the Python interpreter from the Lean MCP virtual environment. Temporary
proofs live below lean/.lake and are removed; no research source is edited.
This is a tool compatibility check, not a new mathematical result.
"""

import argparse
import asyncio
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

from mcp import ClientSession, StdioServerParameters
from mcp.client.stdio import stdio_client


ROOT = Path(__file__).resolve().parents[1]
FIXTURE = """import Subtail.TwoState

namespace SubtailMcpPilot
theorem identity (n : Nat) : n = n := by
  rfl
end SubtailMcpPilot
"""
EXTERNAL_SEARCH = {
    "lean_leansearch", "lean_loogle", "lean_leanfinder",
    "lean_state_search", "lean_hammer_premise",
}


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def command(args, cwd, env=None):
    result = subprocess.run(args, cwd=cwd, env=env, text=True,
                            capture_output=True, timeout=120, check=True)
    return result.stdout.strip()


async def exercise(configuration, project, fixture):
    transport = configuration["transport"]
    require(transport["type"] == "stdio", "This pilot expects a local stdio server")
    environment = {**os.environ, **(transport.get("env") or {})}
    params = StdioServerParameters(
        command=transport["command"], args=transport.get("args", []),
        env=environment, cwd=str(project.parent),
    )
    async with stdio_client(params) as (reader, writer):
        async with ClientSession(reader, writer, read_timeout_seconds=90) as session:
            initialized = (await session.initialize()).model_dump(by_alias=True)
            listed = (await session.list_tools()).model_dump(by_alias=True)
            names = {tool["name"] for tool in listed["tools"]}
            needed = {"lean_goal", "lean_diagnostic_messages", "lean_multi_attempt",
                      "lean_verify", "lean_run_code"}
            require(needed <= names, "Required proof tools are missing")
            require(not names & EXTERNAL_SEARCH, "Pilot must use local proof tools only")

            async def call(name, arguments):
                result = (await session.call_tool(name, arguments)).model_dump(by_alias=True)
                require(not result.get("isError"), f"{name} returned an MCP error")
                value = result.get("structuredContent")
                require(isinstance(value, dict), f"{name} returned no structured result")
                return value.get("result", value)

            diagnostics = await call("lean_diagnostic_messages", {
                "file_path": str(fixture), "timeout_s": 30,
            })
            require(diagnostics.get("success") and not diagnostics.get("partial"),
                    "File elaboration did not complete")
            require(not diagnostics.get("items"), "Complete fixture has diagnostics")

            goals = await call("lean_goal", {
                "file_path": str(fixture), "line": 5, "timeout_s": 30,
            })
            require(any("n = n" in goal for goal in goals.get("goals_before", [])),
                    "Expected proof goal was not returned")
            require(goals.get("goals_after") == [], "rfl did not close the goal")

            attempts = await call("lean_multi_attempt", {
                "file_path": str(fixture), "line": 5,
                "snippets": ["rfl", "simp", "exact False.elim (by assumption)"],
            })
            items = attempts["items"]
            require(len(items) == 3, "A trial result is missing")
            for item in items[:2]:
                require(not item["timed_out"] and item["goals"] == []
                        and not item["diagnostics"], "A valid trial did not pass")
            require(any(d["severity"] == "error" for d in items[2]["diagnostics"]),
                    "Invalid trial was not rejected")
            require(fixture.read_text() == FIXTURE, "Trial modified the source file")

            trivial = await call("lean_verify", {
                "file_path": str(fixture), "theorem_name": "SubtailMcpPilot.identity",
            })
            require(trivial["axioms"] == [], "Identity theorem has unexpected axioms")
            existing = await call("lean_verify", {
                "file_path": str(project / "Subtail/TwoState.lean"),
                "theorem_name": "Subtail.twoStateWitnessCheck_correct",
            })
            require(set(existing["axioms"]) <= {"propext", "Quot.sound", "Classical.choice"},
                    "Existing theorem has a nonstandard axiom")

            code = await call("lean_run_code", {
                "code": "import Subtail.TwoState\nexample : 1 + 1 = 2 := by decide\n",
            })
            require(code.get("success") is True, "Standalone code did not check")
            return {
                "server": initialized["serverInfo"]["version"],
                "local_tools_exposed": len(names),
                "diagnostics_complete_and_clear": True,
                "goal_before": goals["goals_before"], "goal_after": goals["goals_after"],
                "valid_trials": 2, "invalid_trials_rejected": 1,
                "fixture_unchanged": True,
                "identity_axioms": trivial["axioms"],
                "two_state_theorem_axioms": existing["axioms"],
                "standalone_code_checked": True,
            }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--project", type=Path, default=ROOT / "lean")
    parser.add_argument("--codex-server", default="lean-lsp")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    project = args.project.resolve()
    config = json.loads(command(["codex", "mcp", "get", args.codex_server, "--json"], ROOT))
    require(config["enabled"], "Configured server is disabled")
    environment = {**os.environ, **(config["transport"].get("env") or {})}
    lake = shutil.which("lake", path=environment["PATH"])
    require(lake, "Lake is not available to the MCP server")
    version = command([lake, "env", "lean", "--version"], project, environment)
    require("version 4.33.1," in version, "Pilot requires repository-pinned Lean 4.33.1")
    command([lake, "build", "+Subtail.TwoState"], project, environment)
    with tempfile.TemporaryDirectory(prefix="lean-mcp-smoke-", dir=project / ".lake") as scratch:
        fixture = Path(scratch) / "Smoke.lean"
        fixture.write_text(FIXTURE)
        checks = asyncio.run(exercise(config, project, fixture))
    command([lake, "env", "leanchecker", "Subtail.TwoState"], project, environment)
    result = {
        "status": "PASS", "scope": "Local MCP compatibility, not new mathematical evidence",
        "lean_version": version,
        "source_revision": command(["git", "rev-parse", "HEAD"], project),
        "packages": {name: importlib.metadata.version(name)
                     for name in ("lean-lsp-mcp", "leanclient", "mcp")},
        "fixture_sha256": hashlib.sha256(FIXTURE.encode()).hexdigest(),
        "two_state_kernel_replay": "PASS", "checks": checks,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
