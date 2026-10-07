module

public import GinibrePoincare.Analysis.RadiusDifferential

@[expose] public section

open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section

/-- Scaled centered particle coordinate appearing in the radius gradient. -/
def centeredScaled {n : ℕ} (z : Configuration n) (j : Fin n) : ℂ :=
  (n : ℂ) * z j - coordinateSum z

@[simp] theorem centeredScaled_sum {n : ℕ} (z : Configuration n) :
    (∑ j, centeredScaled z j) = 0 := by
  simp [centeredScaled, Finset.sum_sub_distrib, ← Finset.mul_sum, coordinateSum]

@[simp] theorem centeredScaled_conj_sum {n : ℕ} (z : Configuration n) :
    (∑ j, conj (centeredScaled z j)) = 0 := by
  rw [← map_sum, centeredScaled_sum, map_zero]

/-- Exact squared gradient normalization of the centered quadratic form. -/
theorem centeredScaled_norm_sum (n : ℕ) (z : Configuration n) :
    (∑ j, centeredScaled z j * conj (centeredScaled z j)) =
      (n : ℂ) * complexRadius n z := by
  have he (j : Fin n) : centeredScaled z j * conj (centeredScaled z j) =
      (n : ℂ)^2 * (z j * conj (z j)) -
        (n : ℂ) * z j * conj (coordinateSum z) -
        (n : ℂ) * coordinateSum z * conj (z j) +
        coordinateSum z * conj (coordinateSum z) := by
    simp only [centeredScaled, map_sub, map_mul, map_natCast]
    ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [complexRadius_eq]
  unfold radiusBilinear coordinateSum
  rw [← map_sum]
  ring

/-- Radius derivative along real coordinate directions. -/
theorem radius_gradient_real (n : ℕ) (z : Configuration n) (j : Fin n) :
    fderiv ℝ (complexRadius n) z (realCoordinateDirection j) =
      conj (centeredScaled z j) + centeredScaled z j := by
  rw [realCoordinateDirection, complexRadius_coordinateDirection]
  simp [centeredScaled]

/-- Radius derivative along imaginary coordinate directions. -/
theorem radius_gradient_imaginary (n : ℕ) (z : Configuration n) (j : Fin n) :
    fderiv ℝ (complexRadius n) z (imaginaryCoordinateDirection j) =
      Complex.I * (conj (centeredScaled z j) - centeredScaled z j) := by
  rw [imaginaryCoordinateDirection, complexRadius_coordinateDirection]
  simp [centeredScaled]
  ring

/-- The sum-coordinate and radius gradients have no mixed second-order term. -/
theorem radius_gradient_mixed_sum (n : ℕ) (z : Configuration n) :
    (∑ j : Fin n, (fderiv ℝ (complexRadius n) z (realCoordinateDirection j) +
      Complex.I * fderiv ℝ (complexRadius n) z (imaginaryCoordinateDirection j))) = 0 := by
  have he (j : Fin n) : fderiv ℝ (complexRadius n) z (realCoordinateDirection j) +
      Complex.I * fderiv ℝ (complexRadius n) z (imaginaryCoordinateDirection j) =
        2 * centeredScaled z j := by
    rw [radius_gradient_real, radius_gradient_imaginary]
    linear_combination (conj (centeredScaled z j) - centeredScaled z j) * Complex.I_mul_I
  simp_rw [he]
  rw [← Finset.mul_sum, centeredScaled_sum, mul_zero]

/-- The conjugate-sum coordinate also has no mixed second-order term with the radius. -/
theorem radius_gradient_conj_mixed_sum (n : ℕ) (z : Configuration n) :
    (∑ j : Fin n, (fderiv ℝ (complexRadius n) z (realCoordinateDirection j) -
      Complex.I * fderiv ℝ (complexRadius n) z (imaginaryCoordinateDirection j))) = 0 := by
  have he (j : Fin n) : fderiv ℝ (complexRadius n) z (realCoordinateDirection j) -
      Complex.I * fderiv ℝ (complexRadius n) z (imaginaryCoordinateDirection j) =
        2 * conj (centeredScaled z j) := by
    rw [radius_gradient_real, radius_gradient_imaginary]
    linear_combination -(conj (centeredScaled z j) - centeredScaled z j) * Complex.I_mul_I
  simp_rw [he]
  rw [← Finset.mul_sum, centeredScaled_conj_sum, mul_zero]

/-- The radius carré du champ has the exact CIR coefficient. -/
theorem radius_gradient_square_sum (n : ℕ) (z : Configuration n) :
    (∑ j : Fin n, (
      (fderiv ℝ (complexRadius n) z (realCoordinateDirection j))^2 +
      (fderiv ℝ (complexRadius n) z (imaginaryCoordinateDirection j))^2)) =
        4 * (n : ℂ) * complexRadius n z := by
  have he (j : Fin n) :
      (fderiv ℝ (complexRadius n) z (realCoordinateDirection j))^2 +
      (fderiv ℝ (complexRadius n) z (imaginaryCoordinateDirection j))^2 =
        4 * centeredScaled z j * conj (centeredScaled z j) := by
    rw [radius_gradient_real, radius_gradient_imaginary]
    linear_combination (conj (centeredScaled z j) - centeredScaled z j)^2 * Complex.I_mul_I
  simp_rw [he, mul_assoc]
  rw [← Finset.mul_sum, centeredScaled_norm_sum]

end
end GinibrePoincare
