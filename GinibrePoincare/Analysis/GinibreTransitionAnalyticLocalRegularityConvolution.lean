module

public import GinibrePoincare.Analysis.WeakDerivativeMollification
public import GinibrePoincare.Concrete.Generator

@[expose] public section

/-! Differentiation of genuine mollification for arbitrary locally integrable
values. These identities require no pre-existing weak gradient. -/
open MeasureTheory MeasureTheory.Measure ContinuousLinearMap Filter
open scoped Topology ContDiff Convolution
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1600000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (μ : Measure E) [SFinite μ] [IsAddLeftInvariant μ] [IsNegInvariant μ]

theorem ginibreLocalRegularity_fderiv_convolution_kernel
    (u φ : E → ℝ) (v x : E) (hu : LocallyIntegrable u μ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    fderiv ℝ (φ ⋆[lsmul ℝ ℝ, μ] u) x v =
      ((fun y => fderiv ℝ φ y v) ⋆[lsmul ℝ ℝ, μ] u) x := by
  have hder := hc.hasFDerivAt_convolution_left (lsmul ℝ ℝ)
    (hφ.of_le (by simp)) hu x
  rw [hder.fderiv,convolution_eq_swap]
  have hi := ((hc.fderiv ℝ).convolutionExists_left
    ((lsmul ℝ ℝ).precompL E) (hφ.continuous_fderiv (by simp)) hu x).integrable_swap
  rw [ContinuousLinearMap.integral_apply hi v,convolution_lsmul_swap]
  simp only [precompL_apply,lsmul_apply,smul_eq_mul]

theorem ginibreLocalRegularity_second_convolution_kernel
    (u φ : E → ℝ) (v x : E) (hu : LocallyIntegrable u μ)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    fderiv ℝ (fun y => fderiv ℝ (φ ⋆[lsmul ℝ ℝ, μ] u) y v) x v =
      ((fun y => fderiv ℝ (fun z => fderiv ℝ φ z v) y v) ⋆[lsmul ℝ ℝ, μ] u) x := by
  have hD : ContDiff ℝ ∞ (fun y => fderiv ℝ φ y v) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  have he : (fun y => fderiv ℝ (φ ⋆[lsmul ℝ ℝ, μ] u) y v) =
      (fun y => fderiv ℝ φ y v) ⋆[lsmul ℝ ℝ, μ] u :=
    funext (fun y => ginibreLocalRegularity_fderiv_convolution_kernel μ u φ v y hu hφ hc)
  rw [he]
  exact ginibreLocalRegularity_fderiv_convolution_kernel μ u _ v x hu hD (hc.fderiv_apply ℝ v)

theorem ginibreLocalRegularity_reflected_fderiv
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (x y v : E) :
    fderiv ℝ (fun z => φ (x-z)) y v = -fderiv ℝ φ (x-y) v := by
  have hd := (hφ.differentiable (by simp) (x-y)).hasFDerivAt.comp y
    ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
  change fderiv ℝ (φ ∘ (fun z => x-z)) y v = _
  rw [hd.fderiv]
  simp

theorem ginibreLocalRegularity_reflected_second
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (x y v : E) :
    fderiv ℝ (fun z => fderiv ℝ (fun w => φ (x-w)) z v) y v =
      fderiv ℝ (fun z => fderiv ℝ φ z v) (x-y) v := by
  have hD : ContDiff ℝ ∞ (fun z => fderiv ℝ φ z v) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  have he : (fun z => fderiv ℝ (fun w => φ (x-w)) z v) =
      fun z => -(fderiv ℝ φ (x-z) v) :=
    funext (fun z => ginibreLocalRegularity_reflected_fderiv φ hφ x z v)
  rw [he]
  change fderiv ℝ (-(fun z => fderiv ℝ φ (x-z) v)) y v = _
  rw [fderiv_neg]
  simp only [ContinuousLinearMap.neg_apply]
  rw [ginibreLocalRegularity_reflected_fderiv _ hD x y v,neg_neg]

#print axioms ginibreLocalRegularity_second_convolution_kernel
#print axioms ginibreLocalRegularity_reflected_second
end
end GinibrePoincare
