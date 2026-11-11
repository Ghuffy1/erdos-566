import unittest

from verify import parse_axioms


class AxiomAuditTests(unittest.TestCase):
    def test_standard_axioms(self):
        result = parse_axioms(
            "'Proof.main' depends on axioms: [propext, Classical.choice, Quot.sound]",
            ["Proof.main"],
        )
        self.assertEqual(result["Proof.main"], ["Classical.choice", "Quot.sound", "propext"])

    def test_empty_axioms(self):
        result = parse_axioms("'Proof.identity' does not depend on any axioms", ["Proof.identity"])
        self.assertEqual(result["Proof.identity"], [])

    def test_missing_report_fails(self):
        with self.assertRaisesRegex(ValueError, "Missing axiom reports"):
            parse_axioms("", ["Proof.main"])

    def test_placeholder_fails(self):
        with self.assertRaisesRegex(ValueError, "Additional axiom"):
            parse_axioms("'Proof.main' depends on axioms: [sorryAx]", ["Proof.main"])

    def test_custom_axiom_fails(self):
        with self.assertRaisesRegex(ValueError, "Additional axiom"):
            parse_axioms("'Proof.main' depends on axioms: [Proof.assumption]", ["Proof.main"])


if __name__ == "__main__":
    unittest.main()
