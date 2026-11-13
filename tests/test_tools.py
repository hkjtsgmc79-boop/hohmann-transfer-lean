"""Packaging and log-parser tests, not tests of Lean proof correctness."""
import sys, tempfile, unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from build_support import strip_comments_strings, parse_axioms, public_signatures, generate_exports, inventory, sha256

class ToolTests(unittest.TestCase):
    def test_nested_comments(self):
        self.assertNotIn('sorry',strip_comments_strings('/- a /- sorry -/ b -/ theorem x : True := by trivial'))
    def test_real_token_retained(self):self.assertIn('sorry',strip_comments_strings('theorem x : True := by sorry'))
    def test_line_comments(self):self.assertNotIn('axiom',strip_comments_strings('-- axiom x\nexample : True := by trivial'))
    def test_string_literals(self):self.assertNotIn('admit',strip_comments_strings('#eval "admit"'))
    def test_unterminated(self):
        with self.assertRaises(ValueError):strip_comments_strings('/- never closed')
    def test_axioms_standard(self):
        self.assertTrue(parse_axioms("'A.x' depends on axioms: [propext, Classical.choice, Quot.sound]",['A.x'])['passed'])
    def test_axioms_empty(self):
        self.assertTrue(parse_axioms("'A.x' does not depend on any axioms",['A.x'])['passed'])
    def test_axioms_bad(self):
        self.assertFalse(parse_axioms("'A.x' depends on axioms: [sorryAx]",['A.x'])['passed'])
    def test_axioms_missing(self):self.assertFalse(parse_axioms('', ['A.x'])['passed'])
    def test_axioms_wrapped(self):
        self.assertTrue(parse_axioms("'A.x' depends on axioms:\n[propext,\nQuot.sound]",['A.x'])['passed'])
    def test_signature_body_independent(self):
        a='theorem x (a : ℝ) : a=a := by rfl'
        b='theorem x (a : ℝ) : a=a := by simp'
        self.assertEqual(public_signatures(a),public_signatures(b))
    def test_signature_detects_weakening(self):
        self.assertNotEqual(public_signatures('theorem x : False := by t'),public_signatures('theorem x : True := by t'))
    def test_exports_deterministic(self):
        generate_exports(ROOT);a=sha256(ROOT/'Hohmann_Transfer_H2_All.lean')
        generate_exports(ROOT);self.assertEqual(a,sha256(ROOT/'Hohmann_Transfer_H2_All.lean'))
    def test_inventory(self):
        v=inventory(ROOT);self.assertEqual(v['modules'],11);self.assertEqual(v['forbidden_tokens'],[])
    def test_core_export_independent(self):
        s=(ROOT/'Hohmann_Transfer_H2_Core_All.lean').read_text()
        self.assertNotIn('import HohmannTransfer',s)
        self.assertNotIn('-- SOURCE MODULE: HohmannTransfer/',s)
    def test_H1_theorem_headers_match_baseline(self):
        import zipfile
        with zipfile.ZipFile(ROOT/'baseline/Hohmann_Transfer_H1.zip') as z:
            for p in (ROOT/'HohmannTransfer').glob('*.lean'):
                original=z.read('Hohmann_Transfer_H1/HohmannTransfer/'+p.name).decode()
                self.assertEqual(public_signatures(p.read_text()), public_signatures(original))

if __name__=='__main__':unittest.main()
