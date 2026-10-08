module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryLangevinGlobal
public import GinibrePoincare.Analysis.BakryEmeryRegularizationVolume
@[expose] public section
open MeasureTheory Set
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem bakryEmeryStrongConvex_quadratic_lower_bound (W : E → ℝ) (κ : ℝ)
    (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x-κ/2*‖x‖^2)) (x : E) :
    κ/4*‖x‖^2+W 0-‖fderiv ℝ W 0‖^2/κ ≤ W x := by
  have hD := ((hW.differentiable (by norm_num)) (0:E)).hasFDerivAt.sub
    ((hasStrictFDerivAt_norm_sq (0:E)).hasFDerivAt.const_mul (κ/2))
  have hs := bakryEmery_convex_support hc 0 x hD.differentiableAt
  change (fderiv ℝ (W - fun y => κ/2*‖y‖^2) 0) (x-0) ≤ _ at hs
  rw [hD.fderiv] at hs
  simp only [sub_apply,add_apply,smul_apply,smul_eq_mul,innerSL_apply_apply,inner_zero_left,two_smul,
    mul_zero,sub_zero,norm_zero,zero_pow (by decide : 2 ≠ 0)] at hs
  have hd : -(‖fderiv ℝ W 0‖*‖x‖) ≤ fderiv ℝ W 0 x := by
    exact (abs_le.mp (by simpa only [Real.norm_eq_abs] using (fderiv ℝ W 0).le_opNorm x)).1
  have hm := mul_le_mul_of_nonneg_left hs hκ.le
  have hh := mul_le_mul_of_nonneg_left hd hκ.le
  have hcancel : κ*(‖fderiv ℝ W 0‖^2/κ) = ‖fderiv ℝ W 0‖^2 := mul_div_cancel₀ _ hκ.ne'
  apply (mul_le_mul_iff_right₀ hκ).mp
  nlinarith [sq_nonneg (κ*‖x‖/2-‖fderiv ℝ W 0‖)]

theorem bakryEmeryStrongConvex_density_integrable (W : E → ℝ) (κ : ℝ)
    (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x-κ/2*‖x‖^2)) :
    Integrable (fun x => Real.exp (-W x)) volume := by
  have hg := bakryEmery_gaussian_majorant_integrable (E := E) (κ/4) (by positivity)
  apply (hg.const_mul (Real.exp (‖fderiv ℝ W 0‖^2/κ-W 0))).mono
    (Real.continuous_exp.comp hW.continuous.neg).aestronglyMeasurable
  filter_upwards [] with x
  change ‖Real.exp (-W x)‖ ≤ ‖Real.exp (‖fderiv ℝ W 0‖^2/κ-W 0)*Real.exp (-(κ/4)*‖x‖^2)‖
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  rw [Real.norm_eq_abs,abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)),← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hs := bakryEmeryStrongConvex_quadratic_lower_bound W κ hκ hW hc x
  linarith

theorem bakryEmeryStrongConvex_gibbs_probability (W : E → ℝ) (κ : ℝ)
    (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x-κ/2*‖x‖^2)) :
    IsProbabilityMeasure (bakryEmeryNormalizedGibbs volume W) :=
  bakryEmeryNormalizedGibbs_probability volume W hW.continuous
    (bakryEmeryStrongConvex_density_integrable W κ hκ hW hc)

#print axioms bakryEmeryStrongConvex_quadratic_lower_bound
#print axioms bakryEmeryStrongConvex_density_integrable
#print axioms bakryEmeryStrongConvex_gibbs_probability
end
end GinibrePoincare
