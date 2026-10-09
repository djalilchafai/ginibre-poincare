module
public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryCauchyGreenIBP

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem cauchyGreenPotential_dbar_integral (a : ℂ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) (z : ℂ) :
    planarDbar (cauchyGreenPotential a) z =
      ∫ y : ℂ, cauchyGreenKernel y * planarDbar a (z-y) := by
  have hi (v : ℂ) : Integrable (fun y : ℂ => cauchyGreenKernel y * fderiv ℝ a (z-y) v) volume :=
    ((hc.fderiv_apply ℝ v).convolutionExists_right (ContinuousLinearMap.mul ℝ ℂ)
      cauchyGreenKernel_locallyIntegrable
      ((ha.continuous_fderiv (by simp)).clm_apply continuous_const) z).integrable
  change (1/2 : ℂ)*(fderiv ℝ (cauchyGreenPotential a) z 1 +
    Complex.I*fderiv ℝ (cauchyGreenPotential a) z Complex.I) = _
  rw [cauchyGreenPotential_directional_derivative a ha hc z 1,
    cauchyGreenPotential_directional_derivative a ha hc z Complex.I]
  rw [← integral_const_mul,← integral_add (hi 1) ((hi Complex.I).const_mul Complex.I),
    ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by unfold planarDbar; ring)

theorem planarDbar_sub_left (a : ℂ → ℂ) (ha : Differentiable ℝ a) (z y : ℂ) :
    planarDbar (fun w : ℂ => a (z-w)) y = -planarDbar a (z-y) := by
  have hd := (ha (z-y)).hasFDerivAt.comp y
    ((hasFDerivAt_const z y).sub (hasFDerivAt_id y))
  have he : (fun w : ℂ => a (z-w)) = a ∘ (fun w : ℂ => z-w) := rfl
  simp only [planarDbar, he, hd.fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.neg_apply, zero_sub, map_neg]
  ring

#print axioms cauchyGreenPotential_dbar_integral
#print axioms planarDbar_sub_left
end
end GinibrePoincare
