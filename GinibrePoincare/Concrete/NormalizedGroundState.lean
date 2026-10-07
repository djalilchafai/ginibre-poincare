module

public import GinibrePoincare.Concrete.GroundState
public import GinibrePoincare.Concrete.MeasureModel
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Normalized Vandermonde transform

The scale is the square root of the actual mass of `|V_n|² γ_n`.  The
definition therefore agrees with the ground-state transform once positivity
and finiteness of the mass have been proved.
-/

namespace GinibrePoincare

noncomputable section

/-- Real square-root normalization associated with the raw Ginibre mass. -/
def groundStateNormalization (n : ℕ) : ℝ :=
  Real.sqrt (ginibreNormalizingMass n).toReal

/-- Normalized multiplication by the Vandermonde. -/
def normalizedVandermondeTransform (n : ℕ)
    (f : Configuration n → ℂ) : Configuration n → ℂ :=
  fun z => ((groundStateNormalization n : ℂ)⁻¹) *
    vandermondeTransform f z

/-- Pointwise formula for the normalized transform. -/
theorem normalizedVandermondeTransform_apply (n : ℕ)
    (f : Configuration n → ℂ) (z : Configuration n) :
    normalizedVandermondeTransform n f z =
      ((groundStateNormalization n : ℂ)⁻¹) *
        vandermonde z * f z := by
  unfold normalizedVandermondeTransform vandermondeTransform
  ring

/-- The normalized transform sends symmetric functions to alternating ones. -/
theorem normalizedVandermondeTransform_isAlternating {n : ℕ}
    (f : Configuration n → ℂ) (hf : IsSymmetric f) :
    IsAlternating (normalizedVandermondeTransform n f) := by
  intro σ z
  unfold normalizedVandermondeTransform
  rw [vandermondeTransform_isAlternating f hf σ z]
  ring

end

end GinibrePoincare
