module

public import GinibrePoincare.Analysis.FiniteDimensionalItoConfiguration
public import GinibrePoincare.Analysis.GinibreHamiltonianGenerator
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

open Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem secondDirectionalDerivative_scalar_comp {n : ℕ}
    (f : Configuration n → ℝ) (φ : ℝ → ℝ) (x v : Configuration n)
    (hf : ContDiffAt ℝ 2 f x) (hφ : ContDiffAt ℝ 2 φ (f x)) :
    secondDirectionalDerivative (fun y => φ (f y)) v x =
      deriv (deriv φ) (f x)*(fderiv ℝ f x v)^2 +
        deriv φ (f x)*secondDirectionalDerivative f v x := by
  have hfd := hf.differentiableAt (by norm_num)
  have hφd := hφ.differentiableAt (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have hφ'd : DifferentiableAt ℝ (deriv φ) (f x) :=
    (hφ.derivWithin (m:=1) (by norm_num)).differentiableAt (by norm_num)
  have hEq : (fun y => fderiv ℝ (fun z => φ (f z)) y v) =ᶠ[𝓝 x]
      (fun y => deriv φ (f y)*fderiv ℝ f y v) := by
    have hfn := hf.eventually (by norm_num)
    have hφn := hf.continuousAt.eventually (hφ.eventually (by norm_num))
    filter_upwards [hfn,hφn] with y hy hφy
    have he := ((hφy.differentiableAt (by norm_num)).hasDerivAt.comp_hasFDerivAt y
      (hy.differentiableAt (by norm_num)).hasFDerivAt).fderiv
    exact congrArg (fun L => L v) he
  unfold secondDirectionalDerivative
  rw [hEq.fderiv_eq]
  have hg : DifferentiableAt ℝ (fun y => deriv φ (f y)) x := by
    simpa only [Function.comp_def] using hφ'd.comp x hfd
  rw [fderiv_fun_mul hg
    (hd.clm_apply (differentiableAt_const v))]
  have hfirst := (hφ'd.hasDerivAt.comp_hasFDerivAt x hfd.hasFDerivAt).fderiv
  change fderiv ℝ (fun y => deriv φ (f y)) x = deriv (deriv φ) (f x) • fderiv ℝ f x at hfirst
  rw [hfirst]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring


theorem configurationLaplacian_scalar_comp {n : ℕ}
    (f : Configuration n → ℝ) (φ : ℝ → ℝ) (x : Configuration n)
    (hf : ContDiffAt ℝ 2 f x) (hφ : ContDiffAt ℝ 2 φ (f x)) :
    configurationLaplacian (fun y => φ (f y)) x =
      deriv (deriv φ) (f x)*
        realGradientNormSq f x+
      deriv φ (f x)*configurationLaplacian f x := by
  unfold configurationLaplacian realGradientNormSq
  simp_rw [secondDirectionalDerivative_scalar_comp f φ x _ hf hφ]
  simp only [Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring


theorem fderiv_scalar_comp_apply {n : ℕ}
    (f : Configuration n → ℝ) (φ : ℝ → ℝ) (x v : Configuration n)
    (hf : DifferentiableAt ℝ f x) (hφ : DifferentiableAt ℝ φ (f x)) :
    fderiv ℝ (fun y => φ (f y)) x v = deriv φ (f x)*fderiv ℝ f x v := by
  exact congrArg (fun L => L v) (hφ.hasDerivAt.comp_hasFDerivAt x hf.hasFDerivAt).fderiv

theorem ginibrePregenerator_scalar_comp {n : ℕ}
    (f : Configuration n → ℝ) (φ : ℝ → ℝ) (x : Configuration n)
    (hf : ContDiffAt ℝ 2 f x) (hφ : ContDiffAt ℝ 2 φ (f x)) :
    ginibrePregenerator n (fun y => φ (f y)) x =
      deriv φ (f x)*ginibrePregenerator n f x +
        (1/(n : ℝ))*deriv (deriv φ) (f x)*realGradientNormSq f x := by
  unfold ginibrePregenerator
  rw [configurationLaplacian_scalar_comp f φ x hf hφ]
  simp_rw [fderiv_scalar_comp_apply f φ x _
    (hf.differentiableAt (by norm_num)) (hφ.differentiableAt (by norm_num))]
  simp_rw [← Finset.mul_sum]
  ring

theorem ginibreRealPaperSpeedGenerator_scalar_comp {n : ℕ}
    (α : ℝ) (f : Configuration n → ℝ) (φ : ℝ → ℝ) (x : Configuration n)
    (hf : ContDiffAt ℝ 2 f x) (hφ : ContDiffAt ℝ 2 φ (f x)) :
    ginibreRealPaperSpeedGenerator n α (fun y => φ (f y)) x =
      deriv φ (f x)*ginibreRealPaperSpeedGenerator n α f x +
        (α/(n : ℝ)^2)*deriv (deriv φ) (f x)*realGradientNormSq f x := by
  unfold ginibreRealPaperSpeedGenerator
  rw [ginibrePregenerator_scalar_comp f φ x hf hφ]
  simp only [div_eq_mul_inv,inv_pow]
  ring

end
end GinibrePoincare
