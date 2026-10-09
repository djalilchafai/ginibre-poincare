module

public import GinibrePoincare.Analysis.HermiteWirtinger

@[expose] public section

/-! Actual Wirtinger differentiation of the Gaussian in the Rodrigues formula. -/
open scoped ComplexConjugate ContDiff
namespace GinibrePoincare
namespace ComplexHermite
noncomputable section
set_option backward.isDefEq.respectTransparency false

def rodriguesGaussian (n : ℕ) (z : ℂ) : ℂ :=
  (Real.exp (-(n : ℝ)*Complex.normSq z) : ℂ)

def dholOne (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1/2 : ℂ)*(fderiv ℝ f z 1-Complex.I*fderiv ℝ f z Complex.I)

 theorem contDiff_rodriguesGaussian (n : ℕ) : ContDiff ℝ ∞ (rodriguesGaussian n) := by
  unfold rodriguesGaussian
  have hN : ContDiff ℝ ∞ (Complex.normSq : ℂ → ℝ) := by
    convert! (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff) using 1
  exact Complex.ofRealCLM.contDiff.comp ((contDiff_const.mul hN).exp)

 theorem fderiv_rodriguesGaussian (n : ℕ) (z v : ℂ) :
    fderiv ℝ (rodriguesGaussian n) z v =
      ((-(n : ℝ)*(2*z.re*v.re+2*z.im*v.im)) : ℂ)*rodriguesGaussian n z := by
  have hr := Complex.reCLM.hasFDerivAt (x:=z)
  have hi := Complex.imCLM.hasFDerivAt (x:=z)
  have hn := (hr.mul hr).add (hi.mul hi)
  have he : (fun z : ℂ => z.re*z.re+z.im*z.im) = Complex.normSq := by
    funext z
    simp [Complex.normSq_apply]
  change HasFDerivAt (fun w : ℂ => w.re*w.re+w.im*w.im) _ z at hn
  rw [he] at hn
  have hd := Complex.ofRealCLM.hasFDerivAt.comp z ((hn.const_mul (-(n : ℝ))).exp)
  change HasFDerivAt (rodriguesGaussian n) _ z at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    Complex.ofRealCLM_apply, smul_eq_mul]
  push_cast
  unfold rodriguesGaussian
  push_cast
  ring

 theorem dbarOne_rodriguesGaussian (n : ℕ) (z : ℂ) :
    dbarOnePublic (rodriguesGaussian n) z = -(n : ℂ)*z*rodriguesGaussian n z := by
  unfold dbarOnePublic
  rw [fderiv_rodriguesGaussian, fderiv_rodriguesGaussian]
  simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    mul_one, mul_zero, add_zero, zero_add]
  push_cast
  have he := Complex.re_add_im z
  linear_combination (-(n : ℂ)*rodriguesGaussian n z)*he

 theorem dholOne_rodriguesGaussian (n : ℕ) (z : ℂ) :
    dholOne (rodriguesGaussian n) z = -(n : ℂ)*conj z*rodriguesGaussian n z := by
  unfold dholOne
  rw [fderiv_rodriguesGaussian, fderiv_rodriguesGaussian]
  simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    mul_one, mul_zero, add_zero, zero_add]
  push_cast
  have he := congrArg conj (Complex.re_add_im z)
  simp only [map_add, Complex.conj_ofReal, map_mul, Complex.conj_I] at he
  linear_combination (-(n : ℂ)*rodriguesGaussian n z)*he

end
end ComplexHermite
end GinibrePoincare
