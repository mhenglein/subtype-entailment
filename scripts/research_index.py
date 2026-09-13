"""Canonical research index with supplemental research records.

The historical indexer remains byte-for-byte in research_index_base.py. This
front end adds consolidation, repair and subsequent checked-result records
without duplicating or renumbering the earlier monolithic ledgers.
"""
import re
import sys
import research_index_base as _base
from research_index_base import *

_original_research_records = _base.research_records


def _sync_root():
    # Unit tests patch this module's ROOT. Keep the historical implementation
    # pointed at the same temporary tree before delegating to it.
    _base.ROOT = ROOT


def _add_ledger(records, source):
    if not source.is_file():
        return
    contents = source.read_text()
    for prefix in ("c", "e"):
        anchors = list(re.finditer(r'<a id="(' + prefix + r'\d{3})"></a>', contents))
        for index, match in enumerate(anchors):
            end = anchors[index + 1].start() if index + 1 < len(anchors) else len(contents)
            section = contents[match.end():end]
            section = re.split(r"(?m)^## ", section, maxsplit=1)[0]
            key = match[1].upper()
            if key in records:
                raise ValueError("Duplicate research ID: " + key)
            if not section.strip():
                raise ValueError("Empty research record: " + key)
            records[key] = {
                "id": key,
                "source": str(source.relative_to(ROOT)),
                "reference": str(source.relative_to(ROOT)) + "#" + match[1],
                "content": section.strip(),
            }


def research_records(data):
    _sync_root()
    records = _original_research_records(data)
    for relative in ("research/CONSOLIDATION_2026-09-08.md",
                     "research/REPAIRED_12_14_2026-09-08.md",
                     "research/ONE_FLAG_COUNTING.md",
                     "research/COPY_CYCLES.md",
                     "research/SOURCE_POWER_SCHEMES.md",
                     "research/RECOVERED_SOURCE_WALKS.md",
                     "research/SCHEME_COST_BARRIER.md",
                     "research/TARGET_ANCHOR.md"):
        _add_ledger(records, ROOT / relative)
    return records


# Make the historical CLI use the extension as well.
_base.research_records = research_records


def validate_research_ids(records):
    _sync_root()
    return _base.validate_research_ids(records)


def validate_markdown_links():
    _sync_root()
    return _base.validate_markdown_links()


def markdown_sources():
    _sync_root()
    return _base.markdown_sources()


if __name__ == "__main__":
    _sync_root()
    sys.exit(_base.main())
