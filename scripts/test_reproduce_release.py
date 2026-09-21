"""Negative controls for release evidence: a launcher success cannot hide UNKNOWN."""
import json
import hashlib
from pathlib import Path
import subprocess
import tempfile
import unittest

from check_research_submissions import compare
from reproduce_release import native_case_ids, native_receipt, paper_artifacts, receipt_status


class ReleaseReceiptTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.path = Path(self.temp.name) / "receipt.json"

    def write(self, data):
        self.path.write_text(json.dumps(data))
        return self.path

    def test_zero_exit_cannot_supply_an_incomplete_receipt(self):
        for status in ("UNKNOWN", "FAIL", "NOT_RUN", "RUNNING", "DIAGNOSTIC", None):
            with self.subTest(status=status), self.assertRaises(ValueError):
                receipt_status(self.write({"status": status}))
        self.assertEqual(receipt_status(self.write({"status": "PASS"}))["status"], "PASS")

    def native(self, count, statuses, diagnostic=False):
        rows = [{"id": name, "status": status} for name, status in
                zip(sorted(native_case_ids(diagnostic)), statuses)]
        self.assertEqual(len(rows), count)
        return {"status": "DIAGNOSTIC" if diagnostic else "PASS", "rows": rows,
                "counts": {s: statuses.count(s) for s in ("PASS", "FAIL", "UNKNOWN", "NOT_RUN")},
                "automatic_two_promotion_success": False}

    def test_strict_native_unknown_fails_even_with_pass_header(self):
        data = self.native(14, ["PASS"] * 13 + ["UNKNOWN"])
        with self.assertRaises(ValueError):
            native_receipt(self.write(data))

    def test_missing_duplicate_and_false_counts_fail(self):
        for mutation in ("missing", "duplicate", "count", "wrong-case", "missing-credit", "false-credit"):
            data = self.native(14, ["PASS"] * 14)
            if mutation == "missing":
                data["rows"].pop()
            elif mutation == "duplicate":
                data["rows"][-1]["id"] = data["rows"][0]["id"]
            elif mutation == "count":
                data["counts"]["PASS"] = 15
            elif mutation == "wrong-case":
                data["rows"][-1]["id"] = "unrequested unique case"
            elif mutation == "missing-credit":
                del data["automatic_two_promotion_success"]
            else:
                data["automatic_two_promotion_success"] = True
            with self.subTest(mutation=mutation), self.assertRaises(ValueError):
                native_receipt(self.write(data))

    def test_diagnostic_unknown_is_preserved_without_a_successful_answer(self):
        data = self.native(6, ["UNKNOWN"] * 6, diagnostic=True)
        result = native_receipt(self.write(data), diagnostic=True)
        self.assertEqual(result["status"], "DIAGNOSTIC")
        self.assertEqual(result["counts"]["UNKNOWN"], 6)
        self.assertFalse(result["automatic_two_promotion_success"])
        data["rows"][0]["id"] = "unrequested unique case"
        with self.assertRaises(ValueError):
            native_receipt(self.write(data), diagnostic=True)
        data = self.native(6, ["UNKNOWN"] * 6, diagnostic=True)
        data["rows"][0]["status"] = "FAIL"
        with self.assertRaises(ValueError):
            native_receipt(self.write(data), diagnostic=True)

    def test_corpus_environment_is_ignored_but_semantics_and_source_are_not(self):
        saved = {"status": "PASS", "python": "old", "count": 40, "source_sha256": "abc"}
        current = dict(saved, python="new")
        compare(current, saved, ("python",))
        for changed in ({"count": 39}, {"source_sha256": "def"}, {"status": "UNKNOWN"}):
            with self.subTest(changed=changed), self.assertRaises(ValueError):
                compare(dict(current, **changed), saved, ("python",))


class PaperManifestTests(unittest.TestCase):
    def test_stale_pdf_source_or_commit_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            subprocess.run(["git", "init", "-q", str(root)], check=True)
            sources = {}
            for name in ("manuscript.md", "header.tex", "build.py", "lean-map.json", "references.bib", "references.csl"):
                path = root / "paper" / name
                path.parent.mkdir(exist_ok=True)
                path.write_text("original render input")
                sources[str(path.relative_to(root))] = hashlib.sha256(path.read_bytes()).hexdigest()
            subprocess.run(["git", "add", "paper"], cwd=root, check=True)
            subprocess.run(["git", "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                            "commit", "-qm", "render inputs"], cwd=root, check=True)
            revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
            pdf = root / "output/pdf/subtail-paper.pdf"
            pdf.parent.mkdir(parents=True)
            pdf.write_bytes(b"rendered PDF bytes")
            manifest = pdf.with_name("subtail-paper-manifest.json")
            data = {"sources": sources, "source_files_match_render_revision": True,
                    "repository_revision_at_render": revision, "pdf_sha256": hashlib.sha256(pdf.read_bytes()).hexdigest()}
            manifest.write_text(json.dumps(data))
            self.assertEqual(len(paper_artifacts(root)), 2)
            pdf.write_bytes(b"wrong PDF")
            with self.assertRaisesRegex(ValueError, "PDF"):
                paper_artifacts(root)
            pdf.write_bytes(b"rendered PDF bytes")
            source = root / "paper/manuscript.md"
            source.write_text("later unrendered text")
            with self.assertRaisesRegex(ValueError, "Stale paper source"):
                paper_artifacts(root)
            # Updating only a manifest hash cannot fake committed render provenance.
            data["sources"]["paper/manuscript.md"] = hashlib.sha256(source.read_bytes()).hexdigest()
            manifest.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, "Stale paper source"):
                paper_artifacts(root)


if __name__ == "__main__":
    unittest.main()
