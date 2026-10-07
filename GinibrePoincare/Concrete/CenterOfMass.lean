module

public import GinibrePoincare.Concrete.Configuration
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-!
# Centre of mass

The real and imaginary parts of the coordinate sum are the equality
directions in the optimal Ginibre Poincaré inequality.
-/

open scoped BigOperators

namespace GinibrePoincare

/-- Sum of the particle coordinates. -/
def coordinateSum {n : ℕ} (z : Configuration n) : ℂ :=
  ∑ i : Fin n, z i

/-- Real part of the coordinate sum. -/
def centerOfMassReal {n : ℕ} (z : Configuration n) : ℝ :=
  (coordinateSum z).re

/-- Imaginary part of the coordinate sum. -/
def centerOfMassImag {n : ℕ} (z : Configuration n) : ℝ :=
  (coordinateSum z).im

/-- The coordinate sum is permutation invariant. -/
theorem coordinateSum_permute {n : ℕ}
    (σ : ParticlePermutation n) (z : Configuration n) :
    coordinateSum (permute σ z) = coordinateSum z := by
  unfold coordinateSum
  simpa [permute] using (Equiv.sum_comp σ z)

/-- The real centre-of-mass statistic is symmetric. -/
theorem centerOfMassReal_isSymmetric {n : ℕ} :
    IsSymmetric (fun z : Configuration n => centerOfMassReal z) := by
  intro σ z
  simp [centerOfMassReal, coordinateSum_permute]

/-- The imaginary centre-of-mass statistic is symmetric. -/
theorem centerOfMassImag_isSymmetric {n : ℕ} :
    IsSymmetric (fun z : Configuration n => centerOfMassImag z) := by
  intro σ z
  simp [centerOfMassImag, coordinateSum_permute]

end GinibrePoincare
