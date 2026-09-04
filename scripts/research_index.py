"""Build and validate the collaboration tracker using Python's standard library."""

import argparse
import datetime
import json
from pathlib import Path
import re
import sys
from urllib.parse import unquote, urlsplit


ROOT = Path(__file__).resolve().parents[1]
REGISTRY = ROOT / "research/approaches.json"
INDEX = ROOT / "research/README.md"
STATUSES = ("active", "untried", "blocked", "tried")
OUTCOMES = ("open", "supported", "refuted", "inconclusive")


def local_target(reference, base):
    parsed = urlsplit(reference.strip("<>"))
    if parsed.scheme or parsed.netloc or not parsed.path:
        return None
    target = (base / unquote(parsed.path)).resolve()
    if ROOT != target and ROOT not in target.parents:
        raise ValueError("Local reference leaves the repository: " + reference)
    return target


def validate_registry(data):
    if data.get("version") != 1 or not isinstance(data.get("approaches"), list):
        raise ValueError("Expected version 1 and an approaches list")
    seen = set()
    required = {"id", "title", "status", "outcome", "owner", "updated", "summary",
                "next_step", "record", "evidence", "issue"}
    for row in data["approaches"]:
        if set(row) != required:
            raise ValueError("Approach fields must be: " + ", ".join(sorted(required)))
        key = row["id"]
        if not re.fullmatch(r"A\d{3}", key) or key in seen:
            raise ValueError("Invalid or duplicate approach ID: " + str(key))
        seen.add(key)
        if row["status"] not in STATUSES or row["outcome"] not in OUTCOMES:
            raise ValueError(key + ": invalid status or outcome")
        if row["status"] == "untried" and row["outcome"] != "open":
            raise ValueError(key + ": an untried approach must have an open outcome")
        if row["status"] == "active" and not row["owner"]:
            raise ValueError(key + ": active work needs an owner")
        if row["owner"] is not None and not isinstance(row["owner"], str):
            raise ValueError(key + ": owner must be a name or null")
        datetime.date.fromisoformat(row["updated"])
        for field in ("title", "summary", "next_step", "record"):
            if not isinstance(row[field], str) or not row[field].strip():
                raise ValueError(key + ": missing " + field)
        if not isinstance(row["evidence"], list):
            raise ValueError(key + ": evidence must be a list")
        if row["status"] == "tried" and not row["evidence"]:
            raise ValueError(key + ": tried work needs an evidence link")
        for reference in [row["record"]] + row["evidence"]:
            if not isinstance(reference, str):
                raise ValueError(key + ": references must be strings")
            target = local_target(reference, ROOT)
            if target is None or not target.is_file():
                raise ValueError(key + ": missing repository file: " + reference)
        if row["issue"] is not None and not re.fullmatch(
                r"https://github\.com/mhenglein/subtail/issues/\d+", row["issue"]):
            raise ValueError(key + ": issue must belong to this repository")
    expected = {local_target(row["record"], ROOT) for row in data["approaches"]}
    if len(expected) != len(data["approaches"]):
        raise ValueError("Each approach needs its own unique record")
    actual = set((ROOT / "research/approaches").glob("*.md"))
    if actual != expected:
        raise ValueError("Every approach record must occur exactly once in the registry")


def cell(value):
    return value.replace("|", "\\|").replace("\n", " ")


def render(data):
    rows = data["approaches"]
    counts = {status: sum(r["status"] == status for r in rows) for status in STATUSES}
    lines = ["# Research tracker", "",
             "Problem 1.7 is open. This is the current map of approaches, including unsuccessful work.", "",
             f"**{counts['tried']} tried · {counts['untried']} not tried · {counts['blocked']} blocked · {counts['active']} active**", "",
             "Read [the problem and notation](problem.md), [claims and evidence](claims.md), and [the experiment index](../experiments/README.md).", "",
             "Use [the research plan](PLAN.md) for the eleven proposed angles, priorities, and dependencies, including the Lean workstream.", "",
             "Choose a record below to see its scope, attempt history, evidence, and limitations. All unowned work is available to discuss; nobody has been assigned automatically.", "",
             "## How to read the status", "",
             "- **Not tried:** a proposed approach; reading a related paper does not count as trying it.",
             "- **Active:** someone is currently working on it and is named as owner.",
             "- **Blocked:** a specific dependency prevents the next step; the record says whether any prior attempt exists.",
             "- **Tried:** an attempt and evidence are recorded. This does not mean the problem is solved.", "",
             "Outcomes are separate: **supported** applies to the stated limited claim, **refuted** to the exact failed claim, **inconclusive** to an attempt without a verdict, and **open** to unresolved work. Proof status is recorded in the claims ledger.", ""]
    titles = {"active": "Active work", "untried": "Not tried", "blocked": "Blocked", "tried": "Tried: results and dead ends"}
    for status in STATUSES:
        group = [r for r in rows if r["status"] == status]
        lines += ["## " + titles[status], ""]
        if not group:
            lines += ["None currently.", ""]
            continue
        lines += ["| ID | Approach | Finding / next step | Owner |", "|---|---|---|---|"]
        for row in group:
            discussion = ""
            if row["issue"]:
                number = row["issue"].rsplit("/", 1)[-1]
                discussion = f" · [#{number}]({row['issue']})"
            detail = row["summary"] if status == "tried" else row["next_step"]
            if status == "tried":
                detail = row["outcome"].capitalize() + ": " + detail + " Next: " + row["next_step"]
            elif status == "blocked":
                detail = row["summary"] + " Next: " + row["next_step"]
            path = Path(row["record"]).relative_to("research").as_posix()
            lines.append(f"| {row['id']} | [{cell(row['title'])}]({path}){discussion} | {cell(detail)} | {cell(row['owner'] or 'Unassigned')} |")
        lines.append("")
    lines += ["## Updating the record", "",
              "1. Add a dated attempt to the approach's Markdown record; preserve previous failed and inconclusive attempts.",
              "2. Update its status, outcome, owner, evidence links, and next step in [approaches.json](approaches.json).",
              "3. Update the claims ledger or experiment index if a result changed.",
              "4. Run `python3 scripts/research_index.py` from the repository root, then open a pull request.", "",
              "Use [the contribution guide](../CONTRIBUTING.md). GitHub issues hold discussion; this registry holds the current research status. Closing an issue does not establish a theorem.", "",
              "<!-- Generated by scripts/research_index.py. Edit approaches.json and approach records, then regenerate. -->", ""]
    return "\n".join(lines)


def validate_markdown_links():
    errors = []
    for source in ROOT.rglob("*.md"):
        parts = source.relative_to(ROOT).parts
        if any(p.startswith(".") or p in ("tmp", "__pycache__") for p in parts):
            continue
        for reference in re.findall(r"\]\(([^)]+)\)", source.read_text()):
            try:
                target = local_target(reference, source.parent)
                if target is not None and not target.exists():
                    errors.append(f"{source.relative_to(ROOT)}: {reference}")
            except ValueError as error:
                errors.append(f"{source.relative_to(ROOT)}: {error}")
    if errors:
        raise ValueError("Broken local Markdown paths:\n" + "\n".join(errors))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Validate without rewriting the tracker")
    args = parser.parse_args()
    try:
        data = json.loads(REGISTRY.read_text())
        validate_registry(data)
        output = render(data)
        if args.check:
            if not INDEX.exists() or INDEX.read_text() != output:
                raise ValueError("Tracker is stale. Run python3 scripts/research_index.py")
        else:
            INDEX.write_text(output)
        validate_markdown_links()
    except (ValueError, KeyError, TypeError) as error:
        print(str(error), file=sys.stderr)
        return 1
    print(f"Research tracker valid: {len(data['approaches'])} approaches; local Markdown paths checked.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
