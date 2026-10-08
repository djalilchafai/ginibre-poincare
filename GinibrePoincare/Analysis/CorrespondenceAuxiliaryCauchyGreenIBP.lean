module
public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryCauchyGreenLimit
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Ordinary planar Wirtinger integration by parts with a compact test;
the differentiated function need not have compact support. -/
theorem planarDbar_compact_integrationByParts (f θ : ℂ → ℂ)
    (hf : ContDiff ℝ 1 f) (hθ : ContDiff ℝ 1 θ) (hc : HasCompactSupport θ) :
    (∫ z : ℂ, f z * planarDbar θ z) = -(∫ z : ℂ, planarDbar f z * θ z) := by
  have hdf (v : ℂ) : Continuous (fun z => fderiv ℝ f z v) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdθ (v : ℂ) : Continuous (fun z => fderiv ℝ θ z v) :=
    (hθ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hi1 (v : ℂ) : Integrable (fun z => f z * fderiv ℝ θ z v) volume :=
    (hf.continuous.mul (hdθ v)).integrable_of_hasCompactSupport
      ((hc.fderiv_apply ℝ v).mul_left)
  have hi2 (v : ℂ) : Integrable (fun z => fderiv ℝ f z v * θ z) volume :=
    ((hdf v).mul hθ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hibp (v : ℂ) : (∫ z : ℂ, f z * fderiv ℝ θ z v) =
      -(∫ z : ℂ, fderiv ℝ f z v * θ z) :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (hi2 v) (hi1 v)
      ((hf.continuous.mul hθ.continuous).integrable_of_hasCompactSupport hc.mul_left)
      (fun z _ => (hf.differentiable (by norm_num)).differentiableAt)
      (fun z _ => (hθ.differentiable (by norm_num)).differentiableAt)
  have hleft : (∫ z : ℂ, f z * planarDbar θ z) =
      (1/2 : ℂ) * ((∫ z : ℂ, f z * fderiv ℝ θ z 1) +
        Complex.I*(∫ z : ℂ, f z * fderiv ℝ θ z Complex.I)) := by
    have he : (fun z : ℂ => f z * planarDbar θ z) =
        (fun z : ℂ => (1/2 : ℂ)*(f z*fderiv ℝ θ z 1 +
          Complex.I*(f z*fderiv ℝ θ z Complex.I))) := by
      funext z
      unfold planarDbar
      ring
    rw [he,integral_const_mul,integral_add (hi1 1) ((hi1 Complex.I).const_mul Complex.I),
      integral_const_mul]
  have hright : (∫ z : ℂ, planarDbar f z * θ z) =
      (1/2 : ℂ) * ((∫ z : ℂ, fderiv ℝ f z 1 * θ z) +
        Complex.I*(∫ z : ℂ, fderiv ℝ f z Complex.I * θ z)) := by
    have he : (fun z : ℂ => planarDbar f z * θ z) =
        (fun z : ℂ => (1/2 : ℂ)*(fderiv ℝ f z 1*θ z +
          Complex.I*(fderiv ℝ f z Complex.I*θ z))) := by
      funext z
      unfold planarDbar
      ring
    rw [he,integral_const_mul,integral_add (hi2 1) ((hi2 Complex.I).const_mul Complex.I),
      integral_const_mul]
  rw [hleft,hright,hibp 1,hibp Complex.I]
  ring

theorem cauchyGreenRegularizedKernel_test_identity (τ : ℝ) (hτ : 0 < τ)
    (θ : ℂ → ℂ) (hθ : ContDiff ℝ 1 θ) (hc : HasCompactSupport θ) :
    (∫ z : ℂ, cauchyGreenRegularizedKernel τ z * planarDbar θ z) =
      -(∫ z : ℂ, ((τ / (Real.pi*(Complex.normSq z+τ)^2) : ℝ) : ℂ) * θ z) := by
  rw [planarDbar_compact_integrationByParts _ _
    ((cauchyGreenRegularizedKernel_contDiff τ hτ).of_le (by simp)) hθ hc]
  simp_rw [cauchyGreenRegularizedKernel_dbar τ hτ]

#print axioms planarDbar_compact_integrationByParts
#print axioms cauchyGreenRegularizedKernel_test_identity
end
end GinibrePoincare
