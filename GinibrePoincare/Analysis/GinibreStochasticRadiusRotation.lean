module

public import GinibrePoincare.Analysis.GinibreStochasticPlanarGaussianRotation

@[expose] public section

/-! # Autonomous radial transition laws from genuine isotropic Gaussian noise -/
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 def ginibreNoncentralRadiusLaw (v : ℝ≥0) (m : ℂ) : Measure ℝ :=
  (ginibrePlanarGaussian v).map (fun w => Complex.normSq (m+w))

 theorem ginibreNoncentralRadiusLaw_rotation (v : ℝ≥0) (u m : ℂ) (hu : ‖u‖ = 1) :
    ginibreNoncentralRadiusLaw v (u*m) = ginibreNoncentralRadiusLaw v m := by
  unfold ginibreNoncentralRadiusLaw
  conv_lhs => rw [← ginibrePlanarGaussian_rotation v u hu]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext w
  dsimp
  rw [← mul_add, Complex.normSq_mul, Complex.normSq_eq_norm_sq u, hu]
  norm_num

 theorem ginibreNoncentralRadiusLaw_norm (v : ℝ≥0) (m : ℂ) :
    ginibreNoncentralRadiusLaw v m = ginibreNoncentralRadiusLaw v (‖m‖ : ℂ) := by
  by_cases hm : m = 0
  · simp [hm]
  have hnorm : ‖m‖ ≠ 0 := norm_ne_zero_iff.mpr hm
  let u : ℂ := (starRingEnd ℂ) m / (‖m‖ : ℂ)
  have hu : ‖u‖ = 1 := by simp [u, norm_div, abs_of_nonneg (norm_nonneg m), hnorm]
  have hum : u*m = (‖m‖ : ℂ) := by
    dsimp [u]
    rw [div_mul_eq_mul_div, Complex.conj_mul']
    field_simp
  rw [← hum]
  exact (ginibreNoncentralRadiusLaw_rotation v u m hu).symm

 theorem ginibreNoncentralRadiusLaw_eq_of_normSq_eq (v : ℝ≥0) (m q : ℂ)
    (h : Complex.normSq m = Complex.normSq q) :
    ginibreNoncentralRadiusLaw v m = ginibreNoncentralRadiusLaw v q := by
  rw [ginibreNoncentralRadiusLaw_norm v m, ginibreNoncentralRadiusLaw_norm v q]
  congr 2
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg m, norm_nonneg q]

end
end GinibrePoincare
