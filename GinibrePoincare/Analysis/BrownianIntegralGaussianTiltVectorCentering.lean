module

public import GinibrePoincare.Analysis.BrownianIntegralGaussianTiltVectorLaw

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- True centered-innovation formula for every nonnegative measurable test. -/
theorem gaussianVectorExponentialTilt_centered_lintegral {ι : Type*} [Fintype ι]
    (h : ι → ℝ) (v : ℝ≥0) (f : (ι→ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, ENNReal.ofReal (gaussianVectorExponentialTilt h v x)*
      f (fun i => x i-h i*(v : ℝ)) ∂Measure.pi (fun _ : ι => gaussianReal 0 v)) =
      ∫⁻ x, f x ∂Measure.pi (fun _ : ι => gaussianReal 0 v) := by
  classical
  let Q := (Measure.pi (fun _ : ι => gaussianReal 0 v)).withDensity
    (fun x => ENNReal.ofReal (gaussianVectorExponentialTilt h v x))
  have hmap := gaussianReal_pi_exponential_tilt_centered h v
  have hm : Measurable (fun x : ι→ℝ => fun i => x i-h i*(v : ℝ)) := by fun_prop
  have hh := lintegral_map (μ:=Q) hf hm
  change (∫⁻ x, f x ∂Q.map (fun x i => x i-h i*(v : ℝ))) = _ at hh
  rw [hmap] at hh
  have hfm : Measurable (fun x : ι→ℝ => f (fun i => x i-h i*(v : ℝ))) := by fun_prop
  dsimp only [Q] at hh
  rw [lintegral_withDensity_eq_lintegral_mul _ (by
    unfold gaussianVectorExponentialTilt gaussianExponentialTilt; fun_prop) hfm] at hh
  exact hh.symm

end
end GinibrePoincare
