module

public import GinibrePoincare.Analysis.NonQuadraticWeightedProductMollification
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

@[expose] public section

/-! # Actual complex directional derivative transfer through compact convolution -/
open MeasureTheory MeasureTheory.Measure Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
local instance : IsAddHaarMeasure ((volume : Measure ℂ).prod (volume : Measure ℂ)) := {}

theorem productComplexDirectional_convolution_transfer
    (f k : ℂ × ℂ → ℂ) (hf : ContDiff ℝ 1 f) (hk : ContDiff ℝ 1 k)
    (hfc : HasCompactSupport f) (hkc : HasCompactSupport k) (v x : ℂ × ℂ) :
    (∫ a, f a * fderiv ℝ k (x-a) v ∂((volume : Measure ℂ).prod (volume : Measure ℂ))) =
      ∫ a, fderiv ℝ f a v * k (x-a) ∂((volume : Measure ℂ).prod (volume : Measure ℂ)) := by
  let θ : ℂ × ℂ → ℂ := fun a => k (x-a)
  have ht : ContDiff ℝ 1 θ := hk.comp (contDiff_const.sub contDiff_id)
  have htc : HasCompactSupport θ := hkc.comp_homeomorph (Homeomorph.subLeft x)
  have hdf : Continuous (fun a => fderiv ℝ f a v) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdt : Continuous (fun a => fderiv ℝ θ a v) :=
    (ht.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hθ (a : ℂ × ℂ) : fderiv ℝ θ a v = - fderiv ℝ k (x-a) v := by
    have hd := (hk.differentiable (by norm_num) (x-a)).hasFDerivAt.comp a
      ((hasFDerivAt_const x a).sub (hasFDerivAt_id a))
    rw [show θ = k ∘ (fun a => x-a) from rfl, hd.fderiv]
    simp
  have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := ((volume : Measure ℂ).prod (volume : Measure ℂ)))
    ((hdf.mul ht.continuous).integrable_of_hasCompactSupport htc.mul_left)
    ((hf.continuous.mul hdt).integrable_of_hasCompactSupport (htc.fderiv_apply ℝ v).mul_left)
    ((hf.continuous.mul ht.continuous).integrable_of_hasCompactSupport htc.mul_left)
    (fun a _ => (hf.differentiable (by norm_num)).differentiableAt)
    (fun a _ => (ht.differentiable (by norm_num)).differentiableAt)
  simp_rw [hθ, mul_neg, integral_neg] at hi
  exact neg_injective hi
def productComplexDbar (v w : ℂ × ℂ) (f : ℂ × ℂ → ℂ) (x : ℂ × ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f x v + Complex.I * fderiv ℝ f x w)

theorem productComplexDbar_convolution_transfer
    (f k : ℂ × ℂ → ℂ) (hf : ContDiff ℝ 1 f) (hk : ContDiff ℝ 1 k)
    (hfc : HasCompactSupport f) (hkc : HasCompactSupport k) (v w x : ℂ × ℂ) :
    (∫ a, f a * productComplexDbar v w k (x-a)
      ∂((volume : Measure ℂ).prod (volume : Measure ℂ))) =
      ∫ a, productComplexDbar v w f a * k (x-a)
      ∂((volume : Measure ℂ).prod (volume : Measure ℂ)) := by
  have hl (u : ℂ × ℂ) : Integrable (fun a => f a * fderiv ℝ k (x-a) u)
      ((volume : Measure ℂ).prod (volume : Measure ℂ)) :=
    (hf.continuous.mul (((hk.continuous_fderiv (by norm_num)).clm_apply continuous_const).comp
      (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      (((hkc.fderiv_apply ℝ u).comp_homeomorph (Homeomorph.subLeft x)).mul_left)
  have hr (u : ℂ × ℂ) : Integrable (fun a => fderiv ℝ f a u * k (x-a))
      ((volume : Measure ℂ).prod (volume : Measure ℂ)) :=
    (((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
      (hk.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      ((hkc.comp_homeomorph (Homeomorph.subLeft x)).mul_left)
  have hlf : (fun a => f a * productComplexDbar v w k (x-a)) =
      (fun a => (1 / 2 : ℂ) * ((f a * fderiv ℝ k (x-a) v) +
        Complex.I * (f a * fderiv ℝ k (x-a) w))) := by
    funext a
    unfold productComplexDbar
    ring
  have hrf : (fun a => productComplexDbar v w f a * k (x-a)) =
      (fun a => (1 / 2 : ℂ) * ((fderiv ℝ f a v * k (x-a)) +
        Complex.I * (fderiv ℝ f a w * k (x-a)))) := by
    funext a
    unfold productComplexDbar
    ring
  rw [hlf, hrf, integral_const_mul, integral_const_mul,
    integral_add (hl v) ((hl w).const_mul Complex.I),
    integral_add (hr v) ((hr w).const_mul Complex.I), integral_const_mul, integral_const_mul,
    productComplexDirectional_convolution_transfer f k hf hk hfc hkc v x,
    productComplexDirectional_convolution_transfer f k hf hk hfc hkc w x]

end
end GinibrePoincare
