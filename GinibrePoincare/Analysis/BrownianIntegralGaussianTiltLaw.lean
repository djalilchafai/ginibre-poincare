module

public import GinibrePoincare.Analysis.BrownianIntegralGaussianTiltMoments

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem gaussianPDFReal_exponential_tilt (h : ℝ) (v : ℝ≥0) (hv : v≠0) (x : ℝ) :
    gaussianPDFReal 0 v x*gaussianExponentialTilt h v x = gaussianPDFReal (h*(v : ℝ)) v x := by
  unfold gaussianPDFReal gaussianExponentialTilt
  rw [mul_assoc,← Real.exp_add]
  congr 1
  congr 1
  have hv' : (v : ℝ)≠0 := by exact_mod_cast hv
  field_simp
  ring

/-- Exact Gaussian change of measure, including the degenerate zero-duration case. -/
theorem gaussianReal_exponential_tilt (h : ℝ) (v : ℝ≥0) :
    (gaussianReal 0 v).withDensity (fun x => ENNReal.ofReal (gaussianExponentialTilt h v x)) =
      gaussianReal (h*(v : ℝ)) v := by
  by_cases hv : v=0
  · subst v
    simp [gaussianReal_zero_var, dirac_withDensity, gaussianExponentialTilt]
  · rw [gaussianReal_of_var_ne_zero 0 hv, gaussianReal_of_var_ne_zero _ hv,
      ← withDensity_mul volume (measurable_gaussianPDF 0 v)
        (show Measurable (fun x => ENNReal.ofReal (gaussianExponentialTilt h v x)) by
          unfold gaussianExponentialTilt; fun_prop)]
    congr 1
    funext x
    simp only [Pi.mul_apply, gaussianPDF,← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 v x),
      gaussianPDFReal_exponential_tilt h v hv x]

end
end GinibrePoincare
