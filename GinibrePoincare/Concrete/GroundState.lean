module

public import GinibrePoincare.Concrete.Weights
public import Mathlib.Data.ENNReal.Real
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Vandermonde ground-state transform

The unnormalised transform is multiplication by the holomorphic Vandermonde.
A normalised transform is also defined from the actual mass of
`|V_n|² γ_n`; positivity and finiteness of that mass remain explicit analytic
obligations.
-/

namespace GinibrePoincare

noncomputable section

/-- Multiplication by the Vandermonde determinant. -/
def vandermondeTransform {n : ℕ} (f : Configuration n → ℂ) :
    Configuration n → ℂ :=
  fun z => vandermonde z * f z

/-- Symmetric observables become alternating after multiplication by `V_n`. -/
theorem vandermondeTransform_isAlternating {n : ℕ}
    (f : Configuration n → ℂ) (hf : IsSymmetric f) :
    IsAlternating (vandermondeTransform f) := by
  intro σ z
  unfold vandermondeTransform
  rw [vandermonde_permute σ z, hf σ z]
  ring

/-- Pointwise squared-modulus identity for the unnormalised transform. -/
theorem normSq_vandermondeTransform {n : ℕ}
    (f : Configuration n → ℂ) (z : Configuration n) :
    Complex.normSq (vandermondeTransform f z) =
      vandermondeWeight z * Complex.normSq (f z) := by
  simp [vandermondeTransform, vandermondeWeight, Complex.normSq_mul]

end

end GinibrePoincare
