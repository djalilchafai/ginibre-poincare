module

public import GinibrePoincare.Analysis.HermiteRodriguesGaussian

@[expose] public section

/-! Literal iterated Wirtinger derivatives of the Gaussian. -/
open scoped ComplexConjugate ContDiff
namespace GinibrePoincare
namespace ComplexHermite
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem dholOne_mul {f g : ℂ → ℂ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (z : ℂ) :
    dholOne (fun w => f w*g w) z=dholOne f z*g z+f z*dholOne g z := by
  change dholOne (f*g) z = _
  rw [dholOne, dholOne, dholOne, fderiv_mul (hf z) (hg z)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem dholOne_const_mul {f : ℂ → ℂ} (hf : Differentiable ℝ f) (c z : ℂ) :
    dholOne (fun w => c*f w) z = c*dholOne f z := by
  unfold dholOne
  rw [fderiv_const_mul (hf z)]
  simp only [smul_apply, smul_eq_mul]
  ring

theorem dbarOne_const_mul {f : ℂ → ℂ} (hf : Differentiable ℝ f) (c z : ℂ) :
    dbarOnePublic (fun w => c*f w) z = c*dbarOnePublic f z := by
  unfold dbarOnePublic
  rw [fderiv_const_mul (hf z)]
  simp only [smul_apply, smul_eq_mul]
  ring

theorem dholOne_conj_pow (q : ℕ) (z : ℂ) :
    dholOne (fun w => conj w^q) z=0 := by
  unfold dholOne
  have h := ((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt (x:=z)).pow q
  change HasFDerivAt (fun w : ℂ => conj w^q) _ z at h
  rw [h.fderiv]
  simp only [smul_apply, smul_eq_mul, nsmul_eq_mul]
  change (1/2 : ℂ)*((q : ℂ)*conj z^(q-1)*conj 1-
    Complex.I*((q : ℂ)*conj z^(q-1)*conj Complex.I))=0
  simp only [map_one, Complex.conj_I, mul_one]
  linear_combination ((q : ℂ)*conj z^(q-1)/2)*Complex.I_sq

theorem iterate_dholOne_rodriguesGaussian (n q : ℕ) :
    dholOne^[q] (rodriguesGaussian n) =
      fun z => (-(n : ℂ))^q*conj z^q*rodriguesGaussian n z := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Function.iterate_succ_apply', ih]
    funext z
    have hG := (contDiff_rodriguesGaussian n).differentiable (by simp)
    have hpow : Differentiable ℝ (fun w : ℂ => conj w^q) := Complex.conjCLE.differentiable.pow q
    rw [show (fun z => (-(n : ℂ))^q*conj z^q*rodriguesGaussian n z) =
      (fun z => (-(n : ℂ))^q*(conj z^q*rodriguesGaussian n z)) by funext w; ring,
      dholOne_const_mul (hpow.fun_mul hG), dholOne_mul hpow hG,
      dholOne_conj_pow, dholOne_rodriguesGaussian]
    simp only [zero_mul, zero_add, pow_succ]
    ring

end
end ComplexHermite
end GinibrePoincare
