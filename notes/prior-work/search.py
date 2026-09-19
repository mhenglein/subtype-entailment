#!/usr/bin/env python3
"""Read-only, bounded retrieval across scholarship and canonical research records."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
import research_index as research  # Reuse the canonical reader; never copy its ledger.


def table_records(path: Path, prefix: str) -> dict[str, dict]:
    records = {}
    for number, line in enumerate(path.read_text().splitlines(), 1):
        cells = [cell.strip() for cell in re.split(r"(?<!\\)\|", line)[1:-1]]
        if not cells or not re.match(rf"^{prefix}\d{{2}}\b", cells[0]):
            continue
        key, _, status = cells[0].partition(" ")
        if key in records:
            raise ValueError(f"Duplicate scholarship ID: {key}")
        records[key] = {
            "id": key, "kind": "failure" if prefix == "F" else "obligation",
            "title": cells[1], "status": status or "OPEN TASK; not assigned",
            "source": str(path.relative_to(ROOT)), "line": number,
            "content": " | ".join(cells),
        }
    return records


def records() -> dict[str, dict]:
    result = research.research_records(json.loads(research.REGISTRY.read_text()))
    for value in result.values():
        value["kind"] = "research"
        value["title"] = value["content"].splitlines()[0].lstrip("# ")
        value["status"] = "Read canonical content for exact evidence and scope"
    for source in json.loads((HERE / "sources.json").read_text())["sources"]:
        key = source["id"]
        if key in result:
            raise ValueError(f"Duplicate scholarship ID: {key}")
        result[key] = {
            **source, "kind": "source", "status": source["source_status"],
            "source": "notes/prior-work/sources.json",
            "content": json.dumps(source, ensure_ascii=False),
        }
    for name, prefix in (("failure-modes.md", "F"), ("open-obligations.md", "O")):
        result.update(table_records(HERE / name, prefix))
    return result


def topics() -> list[dict]:
    return json.loads((HERE / "topics.json").read_text())["topics"]


def validate_links(corpus: dict, topic_rows: list[dict]) -> None:
    seen = set()
    for row in topic_rows:
        if row["key"] in seen:
            raise ValueError("Duplicate topic: " + row["key"])
        seen.add(row["key"])
        for key in row["records"]:
            if key not in corpus:
                raise ValueError(f"Unknown topic reference: {row['key']} -> {key}")
    pattern = r"\b(?:PW-[A-Z]+\d+|F\d{2}|O\d{2})\b"
    for path in HERE.rglob("*.md"):
        for key in set(re.findall(pattern, path.read_text())):
            if key not in corpus:
                raise ValueError(f"Unknown scholarship reference in {path.name}: {key}")


def related(key: str, topic_rows: list[dict]) -> list[str]:
    return sorted({other for row in topic_rows if key in row["records"]
                   for other in row["records"] if other != key})


def search(corpus: dict, topic_rows: list[dict], query: str, limit: int) -> dict:
    terms = re.findall(r"[\w-]+", query.casefold())
    if not terms:
        raise ValueError("Search needs at least one word or ID")
    results = []
    for key, record in corpus.items():
        matching_topics = [row for row in topic_rows if key in row["records"]]
        topic_text = " ".join(row["key"] + " " + " ".join(row["terms"])
                              for row in matching_topics).casefold()
        title = (key + " " + record["title"]).casefold()
        content = record["content"].casefold()
        if not all(term in title or term in content or term in topic_text for term in terms):
            continue
        score = sum(8 * (term in title) + 3 * (term in topic_text) + (term in content)
                    for term in terms)
        compact = {field: record[field] for field in
                   ("id", "kind", "title", "status", "source", "line", "inspection", "url", "dossier")
                   if field in record}
        compact["matched_topics"] = [row["key"] for row in matching_topics]
        compact["excerpt"] = re.sub(r"\s+", " ", record["content"])[:360]
        results.append((score, key, compact))
    results.sort(key=lambda item: (-item[0], item[1]))
    return {"query": query, "total": len(results), "returned": min(limit, len(results)),
            "truncated": len(results) > limit,
            "results": [row[2] for row in results[:limit]],
            "limit": "Lexical/topic retrieval only; no semantic completeness or theorem validation."}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    actions = parser.add_mutually_exclusive_group(required=True)
    actions.add_argument("--lookup", metavar="ID", help="Retrieve a PW/F/O or canonical A/C/E/Q record")
    actions.add_argument("--search", metavar="TERMS", help="All terms must match content, title or linked topic")
    actions.add_argument("--topics", action="store_true", help="Show topic routes and pre-investigation gates")
    actions.add_argument("--check", action="store_true", help="Check topic and scholarship ID references")
    parser.add_argument("--limit", type=int, default=12, help="Maximum search hits, 1–50 (default 12)")
    args = parser.parse_args()
    try:
        if not 1 <= args.limit <= 50:
            raise ValueError("--limit must be between 1 and 50")
        corpus, topic_rows = records(), topics()
        if args.check:
            validate_links(corpus, topic_rows)
            output = {"references": "PASS", "records": len(corpus), "topics": len(topic_rows),
                      "mathematical_review": "NOT PERFORMED"}
        elif args.topics:
            output = {"topics": topic_rows}
        elif args.lookup:
            key = args.lookup.upper()
            if key not in corpus:
                raise ValueError("Unknown record: " + key)
            output = {**corpus[key], "related_records": related(key, topic_rows)}
        else:
            output = search(corpus, topic_rows, args.search, args.limit)
        print(json.dumps(output, indent=2, ensure_ascii=False))
        return 0
    except (ValueError, KeyError, TypeError, OSError) as error:
        print(str(error), file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
