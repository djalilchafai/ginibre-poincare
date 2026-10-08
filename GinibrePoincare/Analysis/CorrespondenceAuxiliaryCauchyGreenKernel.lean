module
public import GinibrePoincare.Analysis.NonQuadraticDbarBochner
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

@[expose] public section
open MeasureTheory Filter
open scoped Convolution ContDiff
namespace GinibrePoincare
noncomputable section

/-- The genuine planar Cauchy–Green fundamental kernel, totalized at zero. -/
def cauchyGreenKernel (z : ℂ) : ℂ := (Real.pi : ℂ)⁻¹ * z⁻¹

theorem cauchyGreenKernel_locallyIntegrable : LocallyIntegrable cauchyGreenKernel volume := by
  apply locallyIntegrable_of_norm_le_rpow
    (E := ℂ) (C := Real.pi⁻¹) (α := (1 : ℝ))
  · norm_num [Complex.finrank_real_complex]
  · exact ae_of_all _ (fun z => by
      simp [cauchyGreenKernel,norm_mul,norm_inv,Complex.norm_real,
        Real.norm_eq_abs,abs_of_pos Real.pi_pos,Real.rpow_neg_one])
  · exact ((measurable_const.mul measurable_inv) : Measurable cauchyGreenKernel).aestronglyMeasurable
  · norm_num [Complex.finrank_real_complex]

/-- Actual Cauchy–Green integral for a planar source. -/
def cauchyGreenPotential (a : ℂ → ℂ) (z : ℂ) : ℂ :=
  (cauchyGreenKernel ⋆[ContinuousLinearMap.mul ℝ ℂ,volume] a) z

theorem cauchyGreenPotential_contDiff (a : ℂ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) :
    ContDiff ℝ ∞ (cauchyGreenPotential a) :=
  hc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
    cauchyGreenKernel_locallyIntegrable ha

theorem cauchyGreenPotential_directional_derivative (a : ℂ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) (z v : ℂ) :
    fderiv ℝ (cauchyGreenPotential a) z v =
      ∫ y : ℂ, cauchyGreenKernel y * fderiv ℝ a (z-y) v := by
  have hd := hc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
    cauchyGreenKernel_locallyIntegrable (ha.of_le (by simp)) z
  change fderiv ℝ (cauchyGreenKernel ⋆[ContinuousLinearMap.mul ℝ ℂ,volume] a) z v = _
  rw [hd.fderiv]
  have hi := ((hc.fderiv ℝ).convolutionExists_right
    ((ContinuousLinearMap.mul ℝ ℂ).precompR ℂ) cauchyGreenKernel_locallyIntegrable
    (ha.continuous_fderiv (by simp)) z).integrable
  rw [convolution,ContinuousLinearMap.integral_apply hi v]
  rfl

#print axioms cauchyGreenKernel_locallyIntegrable
#print axioms cauchyGreenPotential_contDiff
#print axioms cauchyGreenPotential_directional_derivative
end
end GinibrePoincare
