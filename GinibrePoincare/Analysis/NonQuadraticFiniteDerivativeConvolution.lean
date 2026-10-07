module

public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

@[expose] public section
open MeasureTheory MeasureTheory.Measure Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 60000
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
theorem finiteComplexDirectional_convolution_transfer
    (μ : Measure E) [IsAddHaarMeasure μ]
    (f k : E → ℂ) (hf : ContDiff ℝ 1 f) (hk : ContDiff ℝ 1 k)
    (hfc : HasCompactSupport f) (hkc : HasCompactSupport k) (v x : E) :
    (∫ a, f a * fderiv ℝ k (x-a) v ∂μ) =
      ∫ a, fderiv ℝ f a v * k (x-a) ∂μ := by
  let θ : E → ℂ := fun a => k (x-a)
  have ht : ContDiff ℝ 1 θ := hk.comp (contDiff_const.sub contDiff_id)
  have htc : HasCompactSupport θ := hkc.comp_homeomorph (Homeomorph.subLeft x)
  have hdf : Continuous (fun a => fderiv ℝ f a v) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdt : Continuous (fun a => fderiv ℝ θ a v) :=
    (ht.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hθ (a : E) : fderiv ℝ θ a v = - fderiv ℝ k (x-a) v := by
    have hd := (hk.differentiable (by norm_num) (x-a)).hasFDerivAt.comp a
      ((hasFDerivAt_const x a).sub (hasFDerivAt_id a))
    rw [show θ = k ∘ (fun a => x-a) from rfl, hd.fderiv]
    simp
  have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := μ)
    ((hdf.mul ht.continuous).integrable_of_hasCompactSupport htc.mul_left)
    ((hf.continuous.mul hdt).integrable_of_hasCompactSupport (htc.fderiv_apply ℝ v).mul_left)
    ((hf.continuous.mul ht.continuous).integrable_of_hasCompactSupport htc.mul_left)
    (fun a _ => (hf.differentiable (by norm_num)).differentiableAt)
    (fun a _ => (ht.differentiable (by norm_num)).differentiableAt)
  simp_rw [hθ, mul_neg, integral_neg] at hi
  exact neg_injective hi
def finiteComplexDbar (v w : E) (f : E → ℂ) (x : E) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f x v + Complex.I * fderiv ℝ f x w)

theorem finiteComplexDbar_convolution_transfer
    (μ : Measure E) [IsAddHaarMeasure μ]
    (f k : E → ℂ) (hf : ContDiff ℝ 1 f) (hk : ContDiff ℝ 1 k)
    (hfc : HasCompactSupport f) (hkc : HasCompactSupport k) (v w x : E) :
    (∫ a, f a * finiteComplexDbar v w k (x-a)
      ∂μ) =
      ∫ a, finiteComplexDbar v w f a * k (x-a)
      ∂μ := by
  have hl (u : E) : Integrable (fun a => f a * fderiv ℝ k (x-a) u)
      μ :=
    (hf.continuous.mul (((hk.continuous_fderiv (by norm_num)).clm_apply continuous_const).comp
      (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      (((hkc.fderiv_apply ℝ u).comp_homeomorph (Homeomorph.subLeft x)).mul_left)
  have hr (u : E) : Integrable (fun a => fderiv ℝ f a u * k (x-a))
      μ :=
    (((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
      (hk.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      ((hkc.comp_homeomorph (Homeomorph.subLeft x)).mul_left)
  have hlf : (fun a => f a * finiteComplexDbar v w k (x-a)) =
      (fun a => (1 / 2 : ℂ) * ((f a * fderiv ℝ k (x-a) v) +
        Complex.I * (f a * fderiv ℝ k (x-a) w))) := by
    funext a
    unfold finiteComplexDbar
    ring
  have hrf : (fun a => finiteComplexDbar v w f a * k (x-a)) =
      (fun a => (1 / 2 : ℂ) * ((fderiv ℝ f a v * k (x-a)) +
        Complex.I * (fderiv ℝ f a w * k (x-a)))) := by
    funext a
    unfold finiteComplexDbar
    ring
  rw [hlf, hrf, integral_const_mul, integral_const_mul,
    integral_add (hl v) ((hl w).const_mul Complex.I),
    integral_add (hr v) ((hr w).const_mul Complex.I), integral_const_mul, integral_const_mul,
    finiteComplexDirectional_convolution_transfer μ f k hf hk hfc hkc v x,
    finiteComplexDirectional_convolution_transfer μ f k hf hk hfc hkc w x]

end
end GinibrePoincare
