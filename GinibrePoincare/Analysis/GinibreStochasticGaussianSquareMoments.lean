module

public import GinibrePoincare.Analysis.GinibreStochasticGaussianFourthMoment

@[expose] public section

/-! # Exact second-moment and variance estimates for Gaussian squared increments -/
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem ginibreGaussian_square_memLp_two (v : ℝ≥0) :
    MemLp (fun x : ℝ => x^2) 2 (gaussianReal 0 v) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  have h := integrable_pow_of_mem_interior_integrableExpSet (X := id) (μ := gaussianReal 0 v) (by simp) 4
  simpa only [id_eq, ← pow_mul] using h

 theorem ginibreGaussian_square_variance (v : ℝ≥0) :
    variance (fun x : ℝ => x^2) (gaussianReal 0 v) = 2*(v : ℝ)^2 := by
  rw [variance_eq_sub (ginibreGaussian_square_memLp_two v)]
  simp only [Pi.pow_apply, ← pow_mul]
  rw [ginibreGaussian_centered_fourthMoment, ginibreGaussian_secondMoment]
  norm_num
  ring

 theorem ginibreGaussian_hasLaw_square_memLp_two {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (v : ℝ≥0) (hLaw : HasLaw X (gaussianReal 0 v) P) :
    MemLp (fun ω => (X ω)^2) 2 P := by
  have h := ginibreGaussian_square_memLp_two v
  rw [← hLaw.map_eq] at h
  exact (memLp_map_measure_iff (by fun_prop) hLaw.aemeasurable).mp h

 theorem ginibreGaussian_hasLaw_square_mean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (v : ℝ≥0) (hLaw : HasLaw X (gaussianReal 0 v) P) :
    (∫ ω, (X ω)^2 ∂P) = (v : ℝ) := by
  have h := hLaw.integral_comp (f := fun x : ℝ => x^2) (by fun_prop)
  simpa only [Function.comp_apply, ginibreGaussian_secondMoment, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] using h

 theorem ginibreGaussian_hasLaw_square_variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → ℝ) (v : ℝ≥0) (hLaw : HasLaw X (gaussianReal 0 v) P) :
    variance (fun ω => (X ω)^2) P = 2*(v : ℝ)^2 := by
  have h := ginibreGaussian_square_variance v
  rw [← hLaw.map_eq, variance_map (by fun_prop) hLaw.aemeasurable] at h
  exact h

end
end GinibrePoincare
