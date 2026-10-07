module

public import GinibrePoincare.Analysis.GeneralPotentialVandermondePhase
public import GinibrePoincare.Analysis.NonQuadraticPiSeparatedDerivatives
public import GinibrePoincare.Analysis.GroundStateDbar

@[expose] public section

open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def potentialVandermondeCoefficient (n : ℕ) (V : Potential)
    (g : Configuration n → ℂ) (z : Configuration n) : ℂ :=
  ((Real.sqrt (potentialPartition n V).toReal : ℂ)⁻¹) * vandermonde z * g z

theorem potentialPiHalfWeight_eq (n d : ℕ) (V : Potential) (z : Configuration d) :
    (∏ i, planarPotentialHalfWeight n V (z i)) =
      (Real.exp (-(n : ℝ) * (∑ i, V (z i)) / 2) : ℂ) := by
  unfold planarPotentialHalfWeight
  rw [← Complex.ofReal_prod, ← Real.exp_sum]
  congr 2
  rw [← Finset.sum_div, ← Finset.mul_sum]

theorem potentialVandermondeCoefficient_weighted (n : ℕ) (V : Potential)
    (g : Configuration n → ℂ) (z : Configuration n) :
    potentialVandermondeCoefficient n V g z * (∏ i, planarPotentialHalfWeight n V (z i)) =
      potentialVandermondeMultiplier n V z * g z := by
  rw [potentialPiHalfWeight_eq]
  unfold potentialVandermondeCoefficient potentialVandermondeMultiplier
  ring

theorem piComplexDbar_eq_dbarComponent {d : ℕ} (i : Fin d)
    (f : Configuration d → ℂ) (z : Configuration d) :
    piComplexDbar i f z = dbarComponent f i z := by
  have he (a : ℂ) : Pi.single i a = coordinateDirection i a := by
    funext j
    simp [Pi.single_apply, coordinateDirection, eq_comm]
  simp only [piComplexDbar, finiteComplexDbar, dbarComponent,
    realCoordinateDirection, imaginaryCoordinateDirection, he]

theorem piComplexDbar_potentialVandermondeCoefficient {n : ℕ} (V : Potential)
    (g : Configuration n → ℂ) (hg : Differentiable ℝ g) (i : Fin n) (z : Configuration n) :
    piComplexDbar i (potentialVandermondeCoefficient n V g) z =
      ((Real.sqrt (potentialPartition n V).toReal : ℂ)⁻¹) * vandermonde z * piComplexDbar i g z := by
  simp only [piComplexDbar_eq_dbarComponent]
  apply dbarComponent_holomorphic_mul
    ((differentiable_vandermonde n).const_mul _) hg

theorem potentialVandermondeCoefficient_contDiff {n : ℕ} (V : Potential)
    (g : Configuration n → ℂ) (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 (potentialVandermondeCoefficient n V g) :=
  (contDiff_const.mul ((contDiff_vandermonde n).of_le (by norm_num))).mul hg

theorem potentialVandermondeCoefficient_hasCompactSupport {n : ℕ} (V : Potential)
    (g : Configuration n → ℂ) (hg : HasCompactSupport g) :
    HasCompactSupport (potentialVandermondeCoefficient n V g) :=
  hg.mul_left

end
end GinibrePoincare
