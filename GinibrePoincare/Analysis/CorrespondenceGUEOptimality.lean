module
public import GinibrePoincare.Analysis.CorrespondenceGUEEndpoints
@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem gueFull_poincare_constant_optimal {n : ℕ} (hn : 0<n) (c : ℝ)
    (hc : ∀f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 f →
      (∀σ x, f (guePermute n σ x)=f x) → MemLp f 2 (gueFullMeasure n) →
      MemLp (gradient f) 2 (gueFullMeasure n) →
      (∫x, f x^2 ∂gueFullMeasure n)-(∫x, f x ∂gueFullMeasure n)^2≤
        c*(∫x, ‖gradient f x‖^2 ∂gueFullMeasure n)) : 1/(n : ℝ)≤c := by
  letI := gueFullMeasure_probability hn
  have h := hc (gueCenterCoordinate n) ((gueCenterCoordinate_contDiff n).of_le (by simp))
    (gueCenterCoordinate_symmetric n) (gueCenterCoordinate_memLp hn) (gueCenterCoordinate_gradient_memLp hn)
  rw [gueCenterCoordinate_poincare_equality hn] at h
  simpa only [gueCenterCoordinate_gradient, gueCenterUnit_norm hn, one_pow, integral_const,
    probReal_univ, smul_eq_mul, mul_one] using h

theorem gueFull_lsi_constant_optimal {n : ℕ} (hn : 0<n) (c : ℝ)
    (hc : ∀f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 f →
      (∀σ x, f (guePermute n σ x)=f x) → MemLp f 2 (gueFullMeasure n) →
      MemLp (gradient f) 2 (gueFullMeasure n) →
      squareEntropy (gueFullMeasure n) f≤c*(∫x, ‖gradient f x‖^2 ∂gueFullMeasure n)) :
    2/(n : ℝ)≤c := by
  have h := hc (gueLSIWitness n) ((gueLSIWitness_contDiff n).of_le (by simp))
    (gueLSIWitness_symmetric n) (gueLSIWitness_memLp hn) (gueLSIWitness_gradient_memLp hn)
  rw [gueLSIWitness_lsi_equality hn, gueLSIWitness_gradient_energy hn] at h
  exact (mul_le_mul_iff_left₀ (by positivity : 0<(1/4 : ℝ)*Real.exp ((gueCenterVariance n : ℝ)/2))).mp h

#print axioms gueFull_poincare_constant_optimal
#print axioms gueFull_lsi_constant_optimal
end
end GinibrePoincare
