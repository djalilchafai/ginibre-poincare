module
public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryCauchyGreenKernel
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section
open scoped ComplexConjugate ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def cauchyGreenRegularizedKernel (τ : ℝ) (z : ℂ) : ℂ :=
  conj z / ((Real.pi * (Complex.normSq z+τ) : ℝ) : ℂ)

private theorem normSq_hasFDerivAt (z : ℂ) :
    HasFDerivAt Complex.normSq
      ((2*z.re) • Complex.reCLM + (2*z.im) • Complex.imCLM) z := by
  have h := (Complex.reCLM.hasFDerivAt (x := z)).mul (Complex.reCLM.hasFDerivAt (x := z))
  have h' := (Complex.imCLM.hasFDerivAt (x := z)).mul (Complex.imCLM.hasFDerivAt (x := z))
  convert h.add h' using 1
  · exact funext Complex.normSq_apply
  · ext v
    simp
    ring

theorem cauchyGreenRegularizedKernel_contDiff (τ : ℝ) (hτ : 0 < τ) :
    ContDiff ℝ ∞ (cauchyGreenRegularizedKernel τ) := by
  unfold cauchyGreenRegularizedKernel
  have hn : ContDiff ℝ ∞ Complex.normSq := by
    simpa only [Complex.normSq_apply] using!
      (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
        (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  have hinv := (contDiff_const.mul (hn.add contDiff_const)).inv
    (fun z => (mul_pos Real.pi_pos
      ((Complex.normSq_nonneg z).trans_lt (lt_add_of_pos_right _ hτ))).ne')
  have hc := Complex.conjCLE.contDiff.mul (Complex.ofRealCLM.contDiff.comp hinv)
  simpa only [Function.comp_def, Pi.inv_apply, Complex.conjCLE_apply, Complex.ofRealCLM_apply,
    Complex.ofReal_inv, div_eq_mul_inv] using hc

/-- The actual regularized Cauchy–Green kernel has ∂bar derivative equal
to the normalized positive radial approximate delta kernel. -/
theorem cauchyGreenRegularizedKernel_dbar (τ : ℝ) (hτ : 0 < τ) (z : ℂ) :
    planarDbar (cauchyGreenRegularizedKernel τ) z =
      ((τ / (Real.pi * (Complex.normSq z+τ)^2) : ℝ) : ℂ) := by
  have hd := (Complex.ofRealCLM.hasFDerivAt (x := Real.pi*(Complex.normSq z+τ))).comp z
    (((normSq_hasFDerivAt z).add_const τ).const_mul Real.pi)
  have hden : ((Real.pi*(Complex.normSq z+τ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (mul_pos Real.pi_pos
      ((Complex.normSq_nonneg z).trans_lt (lt_add_of_pos_right _ hτ))).ne'
  have h := (Complex.conjCLE.toContinuousLinearMap.hasFDerivAt (x := z)).mul
    ((hasFDerivAt_inv' (𝕜 := ℝ) hden).comp z hd)
  change (1/2 : ℂ) * (fderiv ℝ (fun w : ℂ => conj w /
    ((Real.pi*(Complex.normSq w+τ) : ℝ) : ℂ)) z 1 +
    Complex.I * fderiv ℝ (fun w : ℂ => conj w /
      ((Real.pi*(Complex.normSq w+τ) : ℝ) : ℂ)) z Complex.I) = _
  simp only [div_eq_mul_inv]
  have he : (fun w : ℂ => conj w * ((Real.pi*(Complex.normSq w+τ) : ℝ) : ℂ)⁻¹) =
      Complex.conjCLE.toContinuousLinearMap * (Inv.inv ∘ Complex.ofRealCLM ∘
        (fun w : ℂ => Real.pi*(Complex.normSq w+τ))) := rfl
  rw [he, h.fderiv]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    Complex.conjCLE_apply, Complex.ofRealCLM_apply, Complex.reCLM_apply,
    Complex.imCLM_apply, smul_eq_mul, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply]
  have hz : Complex.normSq z+τ ≠ 0 :=
    ((Complex.normSq_nonneg z).trans_lt (lt_add_of_pos_right _ hτ)).ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hzc : ((Complex.normSq z+τ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz
  simp only [Function.comp_apply, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply,
    Complex.ofRealCLM_apply, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    mul_one, mul_zero, zero_add, add_zero, map_one, Complex.conj_I]
  simp only [← Complex.ofReal_inv,← Complex.ofReal_mul,← Complex.ofReal_add]
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
      Complex.I_re, Complex.I_im, Complex.inv_re, Complex.inv_im]
  all_goals simp only [Complex.normSq_apply] at *
  all_goals field_simp [Real.pi_ne_zero, hz]
  all_goals norm_num
  all_goals ring

#print axioms cauchyGreenRegularizedKernel_contDiff
#print axioms cauchyGreenRegularizedKernel_dbar
end
end GinibrePoincare
