module
public import GinibrePoincare.Analysis.NonQuadraticFiniteDerivativeConvolution
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.ContDiff.Comp

@[expose] public section
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem real_directional_fderiv (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (x v w : E) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x w = fderiv ℝ (fderiv ℝ f) x w v := by
  have hd := ((hf.fderiv_right (m := 1) (by simp)).differentiable (by simp) x).hasFDerivAt
  have h := ((ContinuousLinearMap.apply ℝ ℂ v).hasFDerivAt).comp x hd
  have he : (fun y => fderiv ℝ f y v) =
      (ContinuousLinearMap.apply ℝ ℂ v) ∘ fderiv ℝ f := rfl
  rw [he,h.fderiv]
  rfl

theorem finiteComplexDbar_contDiff (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (v w : E) :
    ContDiff ℝ ∞ (finiteComplexDbar v w f) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (by simp)
  exact contDiff_const.mul
    ((hd.clm_apply contDiff_const).add (contDiff_const.mul (hd.clm_apply contDiff_const)))

theorem finiteComplexDbar_fderiv (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (x v w b : E) :
    fderiv ℝ (finiteComplexDbar v w f) x b =
      (1/2 : ℂ)*(fderiv ℝ (fderiv ℝ f) x b v +
        Complex.I*fderiv ℝ (fderiv ℝ f) x b w) := by
  have hd := ((hf.fderiv_right (m := 1) (by simp)).differentiable (by simp) x).hasFDerivAt
  have hv := ((ContinuousLinearMap.apply ℝ ℂ v).hasFDerivAt).comp x hd
  have hw := ((ContinuousLinearMap.apply ℝ ℂ w).hasFDerivAt).comp x hd
  have h := (hv.add (hw.const_mul Complex.I)).const_mul (1/2 : ℂ)
  have h' : HasFDerivAt (finiteComplexDbar v w f)
      ((1/2 : ℂ) • ((ContinuousLinearMap.apply ℝ ℂ v).comp (fderiv ℝ (fderiv ℝ f) x) +
        Complex.I • (ContinuousLinearMap.apply ℝ ℂ w).comp (fderiv ℝ (fderiv ℝ f) x))) x := by
    simpa only [finiteComplexDbar,Function.comp_def,Pi.add_apply] using! h
  rw [h'.fderiv]
  simp
  ring

/-- Actual Wirtinger coordinate operators commute on smooth functions,
proved from real second-derivative symmetry. -/
theorem finiteComplexDbar_commute (f : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (v w a b x : E) :
    finiteComplexDbar v w (finiteComplexDbar a b f) x =
      finiteComplexDbar a b (finiteComplexDbar v w f) x := by
  have hsym : IsSymmSndFDerivAt ℝ f x := hf.contDiffAt.isSymmSndFDerivAt (by simp)
  simp only [finiteComplexDbar]
  change (1/2 : ℂ)*(fderiv ℝ (finiteComplexDbar a b f) x v +
    Complex.I*fderiv ℝ (finiteComplexDbar a b f) x w) =
    (1/2 : ℂ)*(fderiv ℝ (finiteComplexDbar v w f) x a +
      Complex.I*fderiv ℝ (finiteComplexDbar v w f) x b)
  rw [finiteComplexDbar_fderiv f hf x a b v,finiteComplexDbar_fderiv f hf x a b w,
    finiteComplexDbar_fderiv f hf x v w a,finiteComplexDbar_fderiv f hf x v w b,
    hsym v a,hsym v b,hsym w a,hsym w b]
  ring

theorem finiteComplexDbar_sub (f g : E → ℂ) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (v w x : E) :
    finiteComplexDbar v w (f-g) x = finiteComplexDbar v w f x - finiteComplexDbar v w g x := by
  simp only [finiteComplexDbar,fderiv_sub (hf x) (hg x),ContinuousLinearMap.sub_apply]
  ring

/-- Removing one genuinely solved component of a smooth closed form makes
every remaining component holomorphic in that coordinate. Closedness may
hold only on the neighborhood under consideration. -/
theorem localDolbeault_smooth_residual_CR (f g u : E → ℂ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hu : ContDiff ℝ ∞ u)
    (v w a b x : E)
    (hsolve : finiteComplexDbar v w u = f)
    (hclosed : finiteComplexDbar a b f x = finiteComplexDbar v w g x) :
    finiteComplexDbar v w (g-finiteComplexDbar a b u) x = 0 := by
  rw [finiteComplexDbar_sub g _ (hg.differentiable (by simp))
    ((finiteComplexDbar_contDiff u hu a b).differentiable (by simp)),
    finiteComplexDbar_commute u hu v w a b x,hsolve,← hclosed,sub_self]

#print axioms real_directional_fderiv
#print axioms finiteComplexDbar_contDiff
#print axioms finiteComplexDbar_fderiv
#print axioms finiteComplexDbar_commute
#print axioms finiteComplexDbar_sub
#print axioms localDolbeault_smooth_residual_CR
end
end GinibrePoincare
