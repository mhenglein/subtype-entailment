#!/usr/bin/env python3
"""Check this documentation register and a finite split regression, not a proof."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
from urllib.parse import unquote, urlsplit


def check(metadata_only: bool = False) -> dict[str, object]:
    root = Path(__file__).resolve().parent
    data = json.loads((root / "sources.json").read_text(encoding="utf-8"))
    sources = data["sources"]
    allowed = {"selected-primary-text", "primary-record", "historical-audit", "unresolved-lead"}
    seen: set[str] = set()
    for source in sources:
        sid = source["id"]
        if not re.fullmatch(r"PW-[A-Z]+[0-9]+", sid) or sid in seen:
            raise ValueError(f"Invalid or duplicate source ID: {sid}")
        seen.add(sid)
        if not isinstance(source["year"], int) or source["inspection"] not in allowed:
            raise ValueError(f"Invalid source metadata: {sid}")
        for field in ("title", "source_status", "locator", "dossier"):
            if not source.get(field):
                raise ValueError(f"Missing {field}: {sid}")
        url = urlsplit(source["url"])
        if url.scheme != "https" or not url.netloc or "token=" in url.query.lower():
            raise ValueError(f"Invalid or credential-bearing URL: {sid}")
        if not metadata_only and not (root / source["dossier"]).is_file():
            raise ValueError(f"Missing dossier for {sid}")
        if source.get("reviewed_at") and not re.fullmatch(r"\d{4}-\d{2}-\d{2}", source["reviewed_at"]):
            raise ValueError(f"Invalid review date for {sid}")
        if not metadata_only and source.get("review_record"):
            if not (root / source["review_record"]).is_file():
                raise ValueError(f"Missing dated review for {sid}")

    # Two genuinely different parses, with no empty factors.
    left, right = {"0", "01"}, {"1", "11"}
    parses = {(a, b) for a in left for b in right if a + b == "011"}
    if parses != {("0", "11"), ("01", "1")}:
        raise ValueError("Split counterexample regression failed")
    # Finite comparison fixture only; the general prefix-free argument is in the note.
    prefix_free = {"0", "10", "11"}
    if any(a != b and b.startswith(a) for a in prefix_free for b in prefix_free):
        raise ValueError("Invalid prefix-free fixture")
    products: dict[str, tuple[str, str]] = {}
    for a in prefix_free:
        for b in {"", "0", "1", "01", "11"}:
            word = a + b
            if word in products and products[word] != (a, b):
                raise ValueError("Prefix-free comparison fixture failed")
            products[word] = (a, b)

    checked_links = 0
    if not metadata_only:
        for document in root.rglob("*.md"):
            text = document.read_text(encoding="utf-8")
            for target in re.findall(r"\[[^\]\n]*\]\(([^)\s]+)\)", text):
                if target.startswith(("https://", "http://", "mailto:", "#")):
                    continue
                path = unquote(target.split("#", 1)[0])
                if path and not (document.parent / path).exists():
                    raise ValueError(f"Broken local target in {document.name}: {target}")
                checked_links += 1
        bibliography = (root / "bibliography.md").read_text(encoding="utf-8")
        if any(sid not in bibliography for sid in seen):
            raise ValueError("Source register and bibliography disagree")
    return {"sources": len(sources), "finite_split_regression": "PASS",
            "prefix_free_fixture": "PASS", "local_link_targets_checked": checked_links,
            "document_checks": "SKIPPED" if metadata_only else "PASS",
            "mathematical_proof_review": "NOT PERFORMED"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--metadata-only", action="store_true",
                        help="Check register and finite fixtures without a full document checkout")
    args = parser.parse_args()
    try:
        print(json.dumps(check(args.metadata_only), indent=2))
    except (KeyError, ValueError, OSError, TypeError) as exc:
        parser.exit(1, f"Scholarship check failed: {exc}\n")
