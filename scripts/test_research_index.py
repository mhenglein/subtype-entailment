"""Regression checks for canonical research navigation and broken handoffs."""

from pathlib import Path
import json
import tempfile
import unittest
from unittest.mock import patch

import research_index as index


class ResearchNavigationTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name).resolve()
        self.addCleanup(patch.stopall)
        patch.object(index, "ROOT", self.root).start()
        self.write("research/claims.md", '<a id="c001"></a>\n### C001 — Exact claim\n\nScope.\n')
        self.write("experiments/README.md", '<a id="e001"></a>\n### E001 — Bounded check\n\nUNKNOWN is not NO.\n')
        self.write("research/conjectures/Q001.md", '# Q001 — Open target\n\nStatus: OPEN\n\nDepends on C001.\n')
        self.write("research/approaches/A001.md", '# A001\n\nHistorical attempt.\n')
        self.data = {"approaches": [{"id": "A001", "record": "research/approaches/A001.md", "owner": None}]}

    def write(self, relative, contents):
        target = self.root / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(contents)

    def test_lookup_preserves_scope_and_stops_at_next_record(self):
        with (self.root / "research/claims.md").open("a") as output:
            output.write('<a id="c002"></a>\n### C002 — Another claim\n\nOther scope.\n')
        records = index.research_records(self.data)
        self.assertIn("Scope.", records["C001"]["content"])
        self.assertNotIn("Other scope", records["C001"]["content"])
        self.assertEqual(records["C002"]["reference"], "research/claims.md#c002")
        self.assertIsNone(records["A001"]["execution"]["owner"])
        self.assertIn("Status: OPEN", records["Q001"]["content"])
        index.validate_research_ids(records)

    def test_duplicate_canonical_id_fails(self):
        self.write("research/claims.md", '<a id="c001"></a>\nFirst.\n<a id="c001"></a>\nSecond.\n')
        with self.assertRaisesRegex(ValueError, "Duplicate research ID"):
            index.research_records(self.data)

    def test_unregistered_reference_fails(self):
        self.write("handoff.md", "Use C099 before attempting Q001.\n")
        with self.assertRaisesRegex(ValueError, "unregistered C099"):
            index.validate_research_ids(index.research_records(self.data))

    def test_scratch_is_not_shared_memory(self):
        self.write("tmp/scratch.md", "Tentative C099.\n")
        index.validate_research_ids(index.research_records(self.data))

    def test_broken_id_anchor_fails_even_when_file_exists(self):
        self.write("handoff.md", "[Claim](research/claims.md#c099)\n")
        with self.assertRaisesRegex(ValueError, "missing ID anchor"):
            index.validate_markdown_links()

    def test_same_file_id_anchor_is_checked(self):
        self.write("handoff.md", "[Claim](#c099)\n")
        with self.assertRaisesRegex(ValueError, "missing ID anchor"):
            index.validate_markdown_links()

    def test_uppercase_fragment_does_not_bypass_anchor_check(self):
        self.write("handoff.md", "[Claim](research/claims.md#C001)\n")
        with self.assertRaisesRegex(ValueError, "missing ID anchor"):
            index.validate_markdown_links()

    def test_general_section_does_not_leak_into_lookup(self):
        with (self.root / "research/claims.md").open("a") as output:
            output.write("\n## General guidance\n\nNot part of the claim.\n")
        record = index.research_records(self.data)["C001"]
        self.assertNotIn("General guidance", record["content"])
        self.assertIn("Scope.", record["content"])

    def test_conjecture_heading_must_match_filename(self):
        self.write("research/conjectures/Q001.md", "# Q002 — Wrong target\n\nStatus: OPEN\n")
        with self.assertRaisesRegex(ValueError, "filename and heading"):
            index.research_records(self.data)


class CurrentClaimStatusTests(unittest.TestCase):
    """Guard known status corrections, not the truth of mathematical proofs."""

    def setUp(self):
        root = Path(__file__).resolve().parents[1]
        with patch.object(index, "ROOT", root):
            data = json.loads((root / "research/approaches.json").read_text())
            self.records = index.research_records(data)

    def test_c044_keeps_equivalence_distinct_from_refuted_q002(self):
        claim = self.records["C044"]["content"]
        self.assertIn("Status: REFUTED", self.records["Q002"]["content"])
        for text in ("WRITTEN PROOF", "equivalence", "C034", "Q002 is REFUTED"):
            self.assertIn(text, claim)
        self.assertNotIn("remains open for larger", claim)

    def test_c045_keeps_conditional_lemma_distinct_from_refuted_q003(self):
        claim = self.records["C045"]["content"]
        self.assertIn("Status: REFUTED", self.records["Q003"]["content"])
        for text in ("WRITTEN PROOF + REPRO", "three hypotheses", "Q003 is REFUTED"):
            self.assertIn(text, claim)
        self.assertNotIn("Q003 remains a", claim)


if __name__ == "__main__":
    unittest.main()
