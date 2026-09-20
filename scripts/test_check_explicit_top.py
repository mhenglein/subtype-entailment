"""Negative controls for the explicit-top declaration audit."""
import unittest

from check_explicit_top import CheckFailure, MODULE, ROOT, SOURCE, source_inventory


class InventoryTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.source = (ROOT / SOURCE).read_text()

    def test_current_core_and_critical_declaration(self):
        inventory = source_inventory(self.source)
        self.assertEqual(len(inventory), 29)
        self.assertEqual(inventory[MODULE + ".entails_iff_projections"], "theorem")

    def test_unused_and_private_custom_declarations_are_rejected(self):
        for addition in ("axiom unrelated : False", "private axiom unrelated : False",
                         "opaque unrelated : Nat := 0"):
            with self.subTest(addition=addition), self.assertRaises(CheckFailure):
                source_inventory(self.source + "\n" + addition + "\n")

    def test_placeholders_are_rejected_even_outside_public_inventory(self):
        for addition in ("private theorem unrelated : False := by sorry",
                         "private def unrelated : False := sorryAx False true"):
            with self.subTest(addition=addition), self.assertRaises(CheckFailure):
                source_inventory(self.source + "\n" + addition + "\n")

    def test_unreviewed_import_is_rejected(self):
        with self.assertRaises(CheckFailure):
            source_inventory(self.source.replace("import Std", "import Std\nimport Subtail"))

    def test_missing_critical_declaration_is_rejected(self):
        with self.assertRaises(CheckFailure):
            source_inventory(self.source.replace("theorem entails_iff_projections", "theorem renamed"))


if __name__ == "__main__":
    unittest.main()
