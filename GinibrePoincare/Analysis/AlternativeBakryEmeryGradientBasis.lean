module
public import GinibrePoincare.Analysis.CompactLipschitzLSIExtension
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
@[expose] public section
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
/-- Coordinate energy in an orthonormal basis is the literal Hilbert gradient
energy, including at points where the total derivative is defined to be zero. -/
theorem bakryEmery_directionalEnergy_orthonormalBasis
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (f : E → ℝ) (x : E) : directionalEnergy b f x = ‖gradient f x‖^2 := by
  have h : InnerProductSpace.toDual ℝ E (gradient f x) = fderiv ℝ f x := by
    simp [gradient]
  unfold directionalEnergy
  rw [← h]
  simpa only [InnerProductSpace.toDual_apply_apply] using b.sum_sq_inner_left (gradient f x)
#print axioms bakryEmery_directionalEnergy_orthonormalBasis
end
end GinibrePoincare
