module
public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryCauchyGreenSmoothSolver

@[expose] public section
open MeasureTheory
open scoped ContDiff Convolution
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The actual Cauchy–Green homotopy on smooth compact functions. -/
theorem cauchyGreenPotential_dbar_source (f : ℂ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (z : ℂ) :
    cauchyGreenPotential (planarDbar f) z = f z := by
  let θ : ℂ → ℂ := fun y => f (z-y)
  have hθ : ContDiff ℝ 1 θ := (hf.of_le (by simp)).comp
    (contDiff_const.sub contDiff_id)
  have hcθ : HasCompactSupport θ := hc.comp_homeomorph (Homeomorph.subLeft z)
  have h := cauchyGreenKernel_fundamental_identity θ hθ hcθ
  have hder (y : ℂ) : planarDbar θ y = -planarDbar f (z-y) :=
    planarDbar_sub_left f (hf.differentiable (by simp)) z y
  simp_rw [hder, mul_neg, integral_neg] at h
  have hh := neg_injective h
  simpa only [cauchyGreenPotential, convolution, ContinuousLinearMap.mul_apply', θ, sub_zero] using! hh

theorem planarDbar_mul (f g : ℂ → ℂ) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (z : ℂ) :
    planarDbar (f*g) z = planarDbar f z * g z + f z * planarDbar g z := by
  rw [planarDbar, fderiv_mul (hf z) (hg z)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, planarDbar]
  ring

/-- The literal boundary correction formula. Its right-hand side contains
no derivative of the rough source, enabling the L² local homotopy. -/
theorem cauchyGreen_cutoff_homotopy (χ g : ℂ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hg : ContDiff ℝ ∞ g) (z : ℂ) :
    cauchyGreenPotential (fun w => χ w * planarDbar g w) z =
      χ z * g z - cauchyGreenPotential (fun w => planarDbar χ w * g w) z := by
  have hχg : HasCompactSupport (χ*g) := hc.mul_right
  have h := cauchyGreenPotential_dbar_source (χ*g) (hχ.mul hg) hχg z
  have he : planarDbar (χ*g) =
      (fun w => planarDbar χ w * g w) + (fun w => χ w * planarDbar g w) := by
    funext w
    exact planarDbar_mul χ g (hχ.differentiable (by simp)) (hg.differentiable (by simp)) w
  have hci : HasCompactSupport (fun w => planarDbar χ w * g w) :=
    (planarDbar_compact χ hc).mul_right
  have hcj : HasCompactSupport (fun w => χ w * planarDbar g w) := hc.mul_right
  have hi := (hci.convolutionExists_right (ContinuousLinearMap.mul ℝ ℂ)
    cauchyGreenKernel_locallyIntegrable
      ((planarDbar_continuous χ (hχ.of_le (by simp))).mul hg.continuous) z).integrable
  have hj := (hcj.convolutionExists_right (ContinuousLinearMap.mul ℝ ℂ)
    cauchyGreenKernel_locallyIntegrable
      (hχ.continuous.mul (planarDbar_continuous g (hg.of_le (by simp)))) z).integrable
  rw [he] at h
  simp only [ContinuousLinearMap.mul_apply'] at hi hj
  simp only [cauchyGreenPotential, convolution, Pi.add_apply, ContinuousLinearMap.mul_apply', mul_add] at h
  rw [integral_add hi hj] at h
  change _ = χ z * g z at h
  change _ = χ z * g z - _
  exact eq_sub_of_add_eq' h

#print axioms cauchyGreenPotential_dbar_source
#print axioms planarDbar_mul
#print axioms cauchyGreen_cutoff_homotopy
end
end GinibrePoincare
