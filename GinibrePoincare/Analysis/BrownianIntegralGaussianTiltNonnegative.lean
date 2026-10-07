module

public import GinibrePoincare.Analysis.BrownianIntegralGaussianTiltMoments
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section

theorem gaussianExponentialTilt_sq_integrable (h : ℝ) (v : ℝ≥0) :
    Integrable (fun x => (gaussianExponentialTilt h v x)^2) (gaussianReal 0 v) := by
  have he (x : ℝ) : (gaussianExponentialTilt h v x)^2 =
      Real.exp (-h^2*(v : ℝ))*Real.exp ((2*h)*x) := by
    rw [gaussianExponentialTilt,pow_two,← Real.exp_add,← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  exact (integrable_exp_mul_gaussianReal (2*h)).const_mul _

theorem gaussianExponentialTilt_lintegral (h : ℝ) (v : ℝ≥0) :
    (∫⁻ x, ENNReal.ofReal (gaussianExponentialTilt h v x) ∂gaussianReal 0 v)=1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (gaussianExponentialTilt_integrable h v)
    (Eventually.of_forall fun x => (Real.exp_pos _).le),gaussianExponentialTilt_integral]
  exact ENNReal.ofReal_one

theorem gaussianExponentialTilt_lintegral_sq (h : ℝ) (v : ℝ≥0) :
    (∫⁻ x, ENNReal.ofReal (gaussianExponentialTilt h v x)^2 ∂gaussianReal 0 v)=
      ENNReal.ofReal (Real.exp (h^2*(v : ℝ))) := by
  have he (x : ℝ) : ENNReal.ofReal (gaussianExponentialTilt h v x)^2 =
      ENNReal.ofReal ((gaussianExponentialTilt h v x)^2) :=
    (ENNReal.ofReal_pow (show 0≤gaussianExponentialTilt h v x from (Real.exp_pos _).le) 2).symm
  simp_rw [he]
  rw [← ofReal_integral_eq_lintegral_ofReal (gaussianExponentialTilt_sq_integrable h v)
    (Eventually.of_forall fun x => sq_nonneg _),gaussianExponentialTilt_integral_sq]

/-- Exact predictable nonnegative normalization on the product law of past
and fresh Gaussian innovation. No boundedness or integrability is assumed. -/
theorem gaussianExponentialTilt_product_lintegral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] (H : α → ℝ) (Z : α → ℝ≥0∞)
    (hH : Measurable H) (hZ : Measurable Z) (v : ℝ≥0) :
    (∫⁻ z, Z z.1*ENNReal.ofReal (gaussianExponentialTilt (H z.1) v z.2)
      ∂μ.prod (gaussianReal 0 v)) = ∫⁻ a, Z a ∂μ := by
  rw [lintegral_prod]
  · congr 1
    funext a
    simp only [Prod.fst,Prod.snd]
    rw [lintegral_const_mul _ (by unfold gaussianExponentialTilt; fun_prop),
      gaussianExponentialTilt_lintegral,mul_one]
  · unfold gaussianExponentialTilt
    fun_prop

/-- Exact second moment on the same genuine product innovation law. -/
theorem gaussianExponentialTilt_product_lintegral_sq {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] (H : α → ℝ) (Z : α → ℝ≥0∞)
    (hH : Measurable H) (hZ : Measurable Z) (v : ℝ≥0) :
    (∫⁻ z, Z z.1*ENNReal.ofReal (gaussianExponentialTilt (H z.1) v z.2)^2
      ∂μ.prod (gaussianReal 0 v)) =
      ∫⁻ a, Z a*ENNReal.ofReal (Real.exp ((H a)^2*(v : ℝ))) ∂μ := by
  rw [lintegral_prod]
  · congr 1
    funext a
    simp only [Prod.fst,Prod.snd]
    rw [lintegral_const_mul _ (by unfold gaussianExponentialTilt; fun_prop),
      gaussianExponentialTilt_lintegral_sq]
  · unfold gaussianExponentialTilt
    fun_prop

end
end GinibrePoincare
