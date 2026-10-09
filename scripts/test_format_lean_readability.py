"""Regression checks for the source-preserving Lean spacing pass."""

import unittest

from format_lean_readability import format_source, format_skip_reason, segments


class ReadabilityFormattingTests(unittest.TestCase):
    def test_dense_math_and_binders(self):
        self.assertEqual(format_source('have h (n:ℕ) : 0<n := by\n  exact ⟨a,b+c⟩\n'),
                         'have h (n : ℕ) : 0<n := by\n  exact ⟨a, b+c⟩\n')

    def test_comments_and_literals_are_preserved(self):
        source = '/-! x+y /- nested,a=b -/ -/\n-- a,b\ndef s := "a,b+c\\\""\n'
        self.assertEqual(format_source(source), source)

    def test_character_literals_and_prime_names(self):
        source = "have h' := foo ',' '+'\nhave h'' := a+b\n"
        self.assertEqual(format_source(source), "have h' := foo ',' '+'\nhave h'' := a+b\n")

    def test_quoted_identifiers(self):
        self.assertEqual(format_source('have «a,b+c» := x+y\n'),
                         'have «a,b+c» := x+y\n')

    def test_compound_notation_and_tactic_combinators(self):
        source = 'variable {E : Type*} (α : ℝ≥0) (p : ℝ≥0∞) (k : ℕ*)\n' \
                 'example := by simp <;> omega\n'
        self.assertEqual(format_source(source), source)

    def test_raw_strings_and_custom_syntax_are_skipped(self):
        for source in ['def text := r#"a,b+c"#\n', 'notation "x+y" => 1\n']:
            self.assertEqual(format_source(source), source)

    def test_imported_compound_operators_remain_intact(self):
        # Each of these is a real token registered in the imported Mathlib tree.
        source = ('have h : f=ᵐ[μ]g := by assumption\n'
                  'have h : f=ᶠ[l]g := by assumption\n'
                  'have h : f≤ᵐ[μ]g := by assumption\n'
                  'have h := A*ᵥv\n'
                  'have h := v+ᵥp\n'
                  'have h := x::ᵥxs\n')
        self.assertEqual(format_source(source), source)

    def test_unknown_symbolic_operators_are_conservative(self):
        source = 'have h := a=ₛb + c*ᵣd ≤ₐe\nhave h := x::ₘxs\n'
        self.assertEqual(format_source(source), source)

    def test_colon_compounds_are_preserved(self):
        source = 'have h := a::b\nhave h := a:::b\nhave h := a:ᵐb\n'
        self.assertEqual(format_source(source), source)

    def test_punctuation_suffixes_are_preserved(self):
        source = 'have h := a,ₛb\nhave h := a,ᵥb\n'
        self.assertEqual(format_source(source), source)

    def test_local_and_scoped_syntax_declarations_are_skipped(self):
        for prefix in ['local notation', 'scoped notation', 'local infixl:50']:
            source = prefix + ' "a,b" => x\nhave h := ⟨a,b⟩\n'
            self.assertEqual(format_source(source), source)

    def test_syntax_quotations_are_skipped(self):
        for source in ['def q := `(term| f (a,b))\n',
                       'def q := foo $[xs],*\n']:
            self.assertEqual(format_source(source), source)

    def test_skip_reasons_are_reportable(self):
        self.assertEqual(format_skip_reason('scoped notation "q" => x\n'),
                         'syntax declaration')
        self.assertEqual(format_skip_reason('def x := r#"a,b"#\n'), 'raw string')
        self.assertEqual(format_skip_reason('def x := `(term| a)\n'),
                         'quotation or antiquotation')
        self.assertIsNone(format_skip_reason('have h (n:ℕ) := x*ᵥy\n'))

    def test_adjacent_ascriptions_are_idempotent(self):
        formatted = format_source('have h := a:b:c\n')
        self.assertEqual(formatted, 'have h := a : b : c\n')
        self.assertEqual(format_source(formatted), formatted)

    def test_no_placeholder_collisions(self):
        source = 'have READABILITYPROTECTED0TOKEN (n:ℕ) := x*ᵥy\n'
        self.assertEqual(format_source(source),
                         'have READABILITYPROTECTED0TOKEN (n : ℕ) := x*ᵥy\n')

    def test_idempotence_and_line_layout(self):
        source = 'have h : a*b+c=d := by\n  exact ⟨h₁,h₂⟩\n'
        formatted = format_source(source)
        self.assertEqual(format_source(formatted), formatted)
        self.assertEqual(formatted.count('\n'), source.count('\n'))

    def test_unclosed_protected_content_is_rejected(self):
        for source in ['/- unfinished', '"unfinished', '«unfinished']:
            with self.assertRaises(ValueError):
                format_source(source)


if __name__ == '__main__':
    unittest.main()
