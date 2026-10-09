module

public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryHolomorphicDerivative

@[expose] public section
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem configuration_real_basis_expansion {n : ℕ} (z : Configuration n) :
    z = ∑ j : Fin n, ((z j).re • (realCoordinateDirection j : Configuration n) +
      (z j).im • (imaginaryCoordinateDirection j : Configuration n)) := by
  funext k
  simp [Finset.sum_apply, realCoordinateDirection, imaginaryCoordinateDirection,
    coordinateDirection, Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, eq_comm, Complex.re_add_im]

/-- The actual joint complex derivative constructed from the real coordinate
partials. -/
def jointComplexDerivative {n : ℕ} (L : Configuration n →L[ℝ] ℂ) :
    Configuration n →L[ℂ] ℂ :=
  ∑ j, (ContinuousLinearMap.proj j).smulRight (L (realCoordinateDirection j))

theorem jointComplexDerivative_restrictScalars {n : ℕ}
    (L : Configuration n →L[ℝ] ℂ)
    (hL : ∀ j, L (imaginaryCoordinateDirection j) =
      Complex.I * L (realCoordinateDirection j)) :
    (jointComplexDerivative L).restrictScalars ℝ = L := by
  ext z
  change (jointComplexDerivative L) z = L z
  unfold jointComplexDerivative
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  conv_rhs => rw [configuration_real_basis_expansion z]
  rw [map_sum]
  simp only [map_add, map_smul, hL]
  apply Finset.sum_congr rfl
  intro j hj
  change z j * L (realCoordinateDirection j) =
    (z j).re • L (realCoordinateDirection j) +
      (z j).im • (Complex.I * L (realCoordinateDirection j))
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp only [smul_eq_mul]
  conv_lhs => rw [← Complex.re_add_im (z j)]
  simp only [add_mul]
  ac_rfl

/-- Coordinate Cauchy–Riemann equations for an actual real Fréchet derivative
imply genuine joint complex differentiability in every finite dimension. -/
theorem hasFDerivAt_complex_of_coordinate_CR {n : ℕ} {f : Configuration n → ℂ}
    {z : Configuration n} {L : Configuration n →L[ℝ] ℂ} (hf : HasFDerivAt f L z)
    (hL : ∀ j, L (imaginaryCoordinateDirection j) =
      Complex.I * L (realCoordinateDirection j)) :
    HasFDerivAt f (jointComplexDerivative L) z :=
  hasFDerivAt_of_restrictScalars ℝ hf (jointComplexDerivative_restrictScalars L hL)

#print axioms configuration_real_basis_expansion
#print axioms jointComplexDerivative_restrictScalars
#print axioms hasFDerivAt_complex_of_coordinate_CR
end
end GinibrePoincare
