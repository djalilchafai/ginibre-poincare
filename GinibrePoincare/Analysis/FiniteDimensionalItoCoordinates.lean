module

public import GinibrePoincare.Analysis.FiniteDimensionalItoTaylor
public import Mathlib.Algebra.BigOperators.Pi

@[expose] public section

namespace GinibrePoincare
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Actual real coordinate Hessian of a finite-dimensional scalar test. -/
def itoHessianEntry (f : (ι → ℝ) → ℝ) (x : ι → ℝ) (i j : ι) : ℝ :=
  fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1)

/-- Actual quadratic Taylor term is the sum of diagonal and cross coordinate terms. -/
theorem itoDirectionalHessian_eq_coordinate_sum (f : (ι → ℝ) → ℝ) (x h : ι → ℝ) :
    itoDirectionalHessian f x h = ∑ i, ∑ j, h i * h j * itoHessianEntry f x i j := by
  unfold itoDirectionalHessian
  rw [iteratedFDeriv_two_apply]
  have hh : h = ∑ i, h i • Pi.single i (1 : ℝ) := by
    simp only [← Pi.single_smul, smul_eq_mul, mul_one]
    exact (Finset.univ_sum_single h).symm
  conv_lhs => rw [hh]
  simp only [map_sum, map_smul, sum_apply, smul_apply,
    smul_eq_mul, itoHessianEntry]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

end
end GinibrePoincare
