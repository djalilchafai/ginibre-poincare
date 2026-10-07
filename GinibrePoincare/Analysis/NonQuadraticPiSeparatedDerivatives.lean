module

public import GinibrePoincare.Analysis.NonQuadraticFiniteDerivativeConvolution
public import GinibrePoincare.Analysis.NonQuadraticPiTensorConvolution
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 60000
set_option backward.isDefEq.respectTransparency false

def piComplexDbar {d : ℕ} (i : Fin d) (f : Configuration d → ℂ) (x : Configuration d) : ℂ :=
  finiteComplexDbar (Pi.single i 1) (Pi.single i Complex.I) f x

theorem piSeparated_fderiv_single {d : ℕ} (φ : Fin d → ℂ → ℂ)
    (hφ : ∀ i, Differentiable ℝ (φ i)) (x : Configuration d) (i : Fin d) (v : ℂ) :
    fderiv ℝ (fun z : Configuration d => ∏ j, φ j (z j)) x (Pi.single i v) =
      (∏ j ∈ Finset.univ.erase i, φ j (x j)) * fderiv ℝ (φ i) (x i) v := by
  have hd := HasFDerivAt.finsetProd (u := Finset.univ) (fun j _ =>
    (hφ j (x j)).hasFDerivAt.comp x ((ContinuousLinearMap.proj j :
      Configuration d →L[ℝ] ℂ).hasFDerivAt))
  change HasFDerivAt (fun z : Configuration d => ∏ j, φ j (z j)) _ x at hd
  rw [hd.fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.single_apply, hji]
  · simp

theorem piSeparated_dbar {d : ℕ} (φ : Fin d → ℂ → ℂ)
    (hφ : ∀ i, Differentiable ℝ (φ i)) (x : Configuration d) (i : Fin d) :
    piComplexDbar i (fun z : Configuration d => ∏ j, φ j (z j)) x =
      (∏ j ∈ Finset.univ.erase i, φ j (x j)) * planarDbar (φ i) (x i) := by
  unfold piComplexDbar finiteComplexDbar planarDbar
  rw [piSeparated_fderiv_single φ hφ x i 1, piSeparated_fderiv_single φ hφ x i Complex.I]
  ring

theorem piComplexDbar_continuous {d : ℕ} (i : Fin d) (f : Configuration d → ℂ)
    (hf : ContDiff ℝ 1 f) : Continuous (piComplexDbar i f) := by
  unfold piComplexDbar finiteComplexDbar
  exact continuous_const.mul (((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const).add
    (continuous_const.mul ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const)))

theorem piComplexDbar_compact {d : ℕ} (i : Fin d) (f : Configuration d → ℂ)
    (hc : HasCompactSupport f) : HasCompactSupport (piComplexDbar i f) :=
  ((hc.fderiv_apply ℝ _).add ((hc.fderiv_apply ℝ _).mul_left)).mul_left
end
end GinibrePoincare
