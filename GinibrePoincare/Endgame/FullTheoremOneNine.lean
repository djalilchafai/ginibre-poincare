module

public import GinibrePoincare.Analysis.GinibreEqualityWeakAffine
public import GinibrePoincare.Analysis.GinibreFullSemigroupDeficitConsequences

@[expose] public section

/-! # Theorem 1.9 on the actual full generator domain

Both sum-of-squares identities hold for every real symmetric generator-domain
observable. Its weak gradient and the convergent Hermite tail follow from graph
membership. Equality in the sharp Poincaré inequality is classified on the
entire weak domain, including non-polynomial observables and L² limits.

## Proof organization

`ginibreFullGenerator_deficit_identities` supplies a weak gradient and the two
Hermite sum-of-squares identities. `ginibreEquality_full_weak_affine_iff` then
identifies the zero deficit with an affine function of the coordinate sum.
The graph hypothesis says that `v` is the generator applied to `u`; it is not
an extra assumption of either deficit identity.

Use `fullTheoremOneNine_named` when consuming individual conclusions: its
record fields avoid remembering the order of the conjunction below. The
original theorem is retained for existing callers.
-/
open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- Full concrete Theorem 1.9, with exact deficit identities and exhaustive
weak affine equality classification. -/
theorem fullTheoremOneNine {n : ℕ} (hn : 0 < n)
    (u v : ginibreFullSymmetricValues n)
    (hgraph : (ginibreFullSymmetricOfReal n u, ginibreFullSymmetricOfReal n v) ∈
      (ginibreFullGenerator n hn).graph) :
    ∃ g : GinibreFullGradientL2 n,
      IsGinibreDistributionalGradient n u.val g ∧
      IsGinibreSymmetricWeakPair (u.val, g) ∧
      Summable (fun k : ℕ => (k : ℝ) *
        positiveHermiteModeMass hn (ginibreFullCenteredTransform n hn u.val) k) ∧
      ginibreWeakEnergy n g - 2 * ginibreL2Variance n hn u.val =
        2 * ‖ginibreFullHolomorphicRemainder n hn u.val‖ ^ 2 +
          4 * modeTail (positiveHermiteModeMass hn (ginibreFullCenteredTransform n hn u.val)) ∧
      ‖v.val‖ ^ 2 - 2 * ginibreWeakEnergy n g =
        ‖v.val + (2 : ℝ) • ginibreFullCenter n hn u.val‖ ^ 2 +
          4 * ‖ginibreFullHolomorphicRemainder n hn u.val‖ ^ 2 +
          8 * modeTail (positiveHermiteModeMass hn (ginibreFullCenteredTransform n hn u.val)) ∧
      (ginibreWeakEnergy n g = 2 * ginibreL2Variance n hn u.val ↔
        ∃ (a : ℝ) (c : ℂ), (u.val : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
          fun z => a + 2 * (c * coordinateSum z).re) := by
  obtain ⟨g, hgradient, hsymmetry, hsummable, hpoincare, hgenerator⟩ :=
    ginibreFullGenerator_deficit_identities hn u v hgraph
  exact ⟨g, hgradient, hsymmetry, hsummable, hpoincare, hgenerator,
    ginibreEquality_full_weak_affine_iff hn u.val g hgradient hsymmetry⟩

/-- The Hermite mode masses of the centered Vandermonde transform of `u`.
This abbreviation introduces no new spectral construction. -/
abbrev ginibreCenteredHermiteMass {n : ℕ} (hn : 0 < n) (u : GinibreFullValueL2 n) :=
  positiveHermiteModeMass hn (ginibreFullCenteredTransform n hn u)

/-- Named conclusions of the two generator-domain deficits, for a fixed weak
gradient `g`. All fields are proved propositions, rather than completion inputs. -/
structure GinibreGeneratorDeficits {n : ℕ} (hn : 0 < n)
    (u v : ginibreFullSymmetricValues n) (g : GinibreFullGradientL2 n) : Prop where
  /-- The gradient is the ordinary distributional gradient of the value. -/
  distributional_gradient : IsGinibreDistributionalGradient n u.val g
  /-- The value and gradient transform together under particle permutations. -/
  symmetric_gradient : IsGinibreSymmetricWeakPair (u.val, g)
  /-- Weighted Hermite masses are summable, so the tail expressions are valid. -/
  weighted_modes_summable : Summable (fun k : ℕ => (k : ℝ) * ginibreCenteredHermiteMass hn u.val k)
  /-- The energy-minus-variance deficit is a sum of nonnegative terms. -/
  poincare_deficit : ginibreWeakEnergy n g - 2 * ginibreL2Variance n hn u.val =
    2 * ‖ginibreFullHolomorphicRemainder n hn u.val‖ ^ 2 +
      4 * modeTail (ginibreCenteredHermiteMass hn u.val)
  /-- The generator-minus-energy deficit uses the same gradient and mode tail. -/
  generator_deficit : ‖v.val‖ ^ 2 - 2 * ginibreWeakEnergy n g =
    ‖v.val + (2 : ℝ) • ginibreFullCenter n hn u.val‖ ^ 2 +
      4 * ‖ginibreFullHolomorphicRemainder n hn u.val‖ ^ 2 +
      8 * modeTail (ginibreCenteredHermiteMass hn u.val)
  /-- Equality is classified as an almost-everywhere affine representative. -/
  equality_iff_affine : ginibreWeakEnergy n g = 2 * ginibreL2Variance n hn u.val ↔
    ∃ (a : ℝ) (c : ℂ), (u.val : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
      fun z => a + 2 * (c * coordinateSum z).re

/-- Theorem 1.9 with named conclusions. For example, after
`obtain ⟨g, result⟩ := fullTheoremOneNine_named hn u v hgraph`, use
`result.poincare_deficit` or `result.equality_iff_affine`. -/
theorem fullTheoremOneNine_named {n : ℕ} (hn : 0 < n)
    (u v : ginibreFullSymmetricValues n)
    (hgraph : (ginibreFullSymmetricOfReal n u, ginibreFullSymmetricOfReal n v) ∈
      (ginibreFullGenerator n hn).graph) :
    ∃ g : GinibreFullGradientL2 n, GinibreGeneratorDeficits hn u v g := by
  obtain ⟨g, hgradient, hsymmetry, hsummable, hpoincare, hgenerator, hequality⟩ :=
    fullTheoremOneNine hn u v hgraph
  exact ⟨g, ⟨hgradient, hsymmetry, hsummable, hpoincare, hgenerator, hequality⟩⟩

end
end GinibrePoincare
