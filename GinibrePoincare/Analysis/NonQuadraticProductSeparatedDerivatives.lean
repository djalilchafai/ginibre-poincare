module

public import GinibrePoincare.Analysis.NonQuadraticProductDerivativeConvolution

@[expose] public section

/-! # Genuine separated kernel identities for both Wirtinger derivatives -/
open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

def productDbarLeft := productComplexDbar (1, 0) (Complex.I, 0)
def productDbarRight := productComplexDbar (0, 1) (0, Complex.I)

theorem productComplexDbar_continuous (v w : ℂ × ℂ) (f : ℂ × ℂ → ℂ)
    (hf : ContDiff ℝ 1 f) : Continuous (productComplexDbar v w f) :=
  continuous_const.mul (((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).add
    (continuous_const.mul ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const)))

theorem productComplexDbar_compact (v w : ℂ × ℂ) (f : ℂ × ℂ → ℂ)
    (hc : HasCompactSupport f) : HasCompactSupport (productComplexDbar v w f) :=
  ((hc.fderiv_apply ℝ v).add (hc.fderiv_apply ℝ w).mul_left).mul_left

theorem productSeparated_fderiv (φ ψ : ℂ → ℂ) (hφ : Differentiable ℝ φ)
    (hψ : Differentiable ℝ ψ) (x : ℂ × ℂ) (u v : ℂ) :
    fderiv ℝ (fun p : ℂ × ℂ => φ p.1 * ψ p.2) x (u,v) =
      fderiv ℝ φ x.1 u * ψ x.2 + φ x.1 * fderiv ℝ ψ x.2 v := by
  have h1 := (hφ x.1).hasFDerivAt.comp x (hasFDerivAt_fst (𝕜 := ℝ) (p := x))
  have h2 := (hψ x.2).hasFDerivAt.comp x (hasFDerivAt_snd (𝕜 := ℝ) (p := x))
  have hm := h1.mul h2
  simp only [Function.comp_def] at hm
  change HasFDerivAt (fun p : ℂ × ℂ => φ p.1 * ψ p.2) _ x at hm
  rw [hm.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul]
  change φ x.1 * fderiv ℝ ψ x.2 v + ψ x.2 * fderiv ℝ φ x.1 u = _
  ring

theorem productDbarLeft_separated (φ ψ : ℂ → ℂ) (hφ : Differentiable ℝ φ)
    (hψ : Differentiable ℝ ψ) (x : ℂ × ℂ) :
    productDbarLeft (fun p : ℂ × ℂ => φ p.1 * ψ p.2) x = planarDbar φ x.1 * ψ x.2 := by
  unfold productDbarLeft productComplexDbar planarDbar
  rw [productSeparated_fderiv φ ψ hφ hψ x 1 0, productSeparated_fderiv φ ψ hφ hψ x Complex.I 0]
  simp only [map_zero, mul_zero, add_zero]
  ring

theorem productDbarRight_separated (φ ψ : ℂ → ℂ) (hφ : Differentiable ℝ φ)
    (hψ : Differentiable ℝ ψ) (x : ℂ × ℂ) :
    productDbarRight (fun p : ℂ × ℂ => φ p.1 * ψ p.2) x = φ x.1 * planarDbar ψ x.2 := by
  unfold productDbarRight productComplexDbar planarDbar
  rw [productSeparated_fderiv φ ψ hφ hψ x 0 1, productSeparated_fderiv φ ψ hφ hψ x 0 Complex.I]
  simp only [map_zero, zero_mul, zero_add]
  ring
end
end GinibrePoincare
