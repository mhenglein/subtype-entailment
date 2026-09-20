"""Failure-path tests for the original-bounds integration gate."""
import unittest

from check_original_bounds import CheckFailure, audit_axioms


class AxiomAuditTests(unittest.TestCase):
    def test_multiline_theorem_and_runtime(self):
        actual = audit_axioms("'M.proof' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n"
                              "'M.run' does not depend on any axioms\n",
                              {"M.proof": "theorem", "M.run": "def"})
        self.assertEqual(actual["M.run"], [])

    def test_missing_or_extra_report_fails(self):
        for output in ("", "'M.other' does not depend on any axioms"):
            with self.assertRaises(CheckFailure):
                audit_axioms(output, {"M.proof": "theorem"})

    def test_duplicate_report_fails(self):
        with self.assertRaises(CheckFailure):
            audit_axioms("'M.proof' does not depend on any axioms\n" * 2, {"M.proof": "theorem"})

    def test_unchecked_axioms_and_runtime_choice_fail(self):
        for kind, axiom in (("def", "Classical.choice"), ("theorem", "sorryAx"),
                            ("theorem", "Lean.ofReduceBool"), ("theorem", "M.assumed")):
            with self.subTest(kind=kind, axiom=axiom), self.assertRaises(CheckFailure):
                audit_axioms(f"'M.item' depends on axioms: [{axiom}]", {"M.item": kind})


if __name__ == "__main__":
    unittest.main()
