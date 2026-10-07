module

public import GinibrePoincare.Analysis.GinibreStochasticBrownianFamilyBracket

@[expose] public section

/-! Mixed shifted moments of an actual finite product Gaussian law. -/
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem ginibreGaussianPi_shifted_crossMoment {ι : Type*} [Fintype ι]
    (v : ℝ≥0) (i j : ι) (hij : i ≠ j) (a b : ℝ) :
    (∫ u : ι → ℝ, (a+u i)*(b+u j) ∂Measure.pi (fun _ : ι => gaussianReal 0 v)) = a*b := by
  let ν := Measure.pi (fun _ : ι => gaussianReal 0 v)
  have hEval (k : ι) : HasLaw (fun u : ι → ℝ => u k) (gaussianReal 0 v) ν :=
    (measurePreserving_eval (fun _ : ι => gaussianReal 0 v) k).hasLaw
  have hMean (k : ι) (c : ℝ) : (∫ u : ι → ℝ, c+u k ∂ν) = c := by
    have h := (hEval k).integral_comp (f := fun x : ℝ => c+x) (by fun_prop)
    simp only [Function.comp_apply] at h
    rw [h]
    have hi : Integrable (fun x : ℝ => x) (gaussianReal 0 v) := IsGaussian.integrable_id
    have he := integral_add (integrable_const c) hi
    rw [he, integral_id_gaussianReal]
    simp
  have hind : iIndepFun (fun k (u : ι → ℝ) => u k) ν := iIndepFun_pi (fun k => aemeasurable_id)
  have hi := (hind.indepFun hij).comp (show Measurable (fun x : ℝ => a+x) by fun_prop)
    (show Measurable (fun x : ℝ => b+x) by fun_prop)
  have h := hi.integral_mul_eq_mul_integral
    ((measurable_const.add (measurable_pi_apply i)).aestronglyMeasurable)
    ((measurable_const.add (measurable_pi_apply j)).aestronglyMeasurable)
  simp only [Function.comp_apply, Pi.mul_apply] at h
  rw [hMean, hMean] at h
  exact h

end
end GinibrePoincare
