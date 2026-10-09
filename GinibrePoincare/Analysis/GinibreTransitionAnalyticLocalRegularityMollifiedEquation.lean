module

public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityConvolution

@[expose] public section

/-! A distributional elliptic equation with locally integrable data becomes a
genuine classical equation under actual compact smooth convolution. No weak
Sobolev regularity or pre-existing gradient is assumed. -/
open MeasureTheory MeasureTheory.Measure ContinuousLinearMap Filter
open scoped Topology ContDiff Convolution
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1800000

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Fintype ι]
  (μ : Measure E) [SFinite μ] [IsAddLeftInvariant μ] [IsNegInvariant μ]

theorem ginibreLocalRegularity_mollified_elliptic_equation
    (u h : E → ℝ) (F : ι → E → ℝ) (v : ι → E)
    (hu : LocallyIntegrable u μ) (hh : LocallyIntegrable h μ)
    (hF : ∀ i, LocallyIntegrable (F i) μ)
    (heq : ∀ θ : E → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ y, u y*(∑ i, fderiv ℝ (fun z => fderiv ℝ θ z (v i)) y (v i)) ∂μ) =
        (∫ y, h y*θ y ∂μ)-∑ i, ∫ y, F i y*fderiv ℝ θ y (v i) ∂μ)
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (x : E) :
    (∑ i, fderiv ℝ (fun y => fderiv ℝ (φ ⋆[lsmul ℝ ℝ, μ] u) y (v i)) x (v i)) =
      (φ ⋆[lsmul ℝ ℝ, μ] h) x+
        ∑ i, fderiv ℝ (φ ⋆[lsmul ℝ ℝ, μ] F i) x (v i) := by
  classical
  let θ : E → ℝ := fun y => φ (x-y)
  have ht : ContDiff ℝ ∞ θ := hφ.comp (contDiff_const.sub contDiff_id)
  have htc : HasCompactSupport θ := hc.comp_homeomorph (Homeomorph.subLeft x)
  have hD (i : ι) : ContDiff ℝ ∞ (fun y => fderiv ℝ φ y (v i)) :=
    (hφ.fderiv_right (by simp)).clm_apply contDiff_const
  have hDD (i : ι) : ContDiff ℝ ∞ (fun y => fderiv ℝ (fun z => fderiv ℝ φ z (v i)) y (v i)) :=
    ((hD i).fderiv_right (by simp)).clm_apply contDiff_const
  have hi (i : ι) : Integrable (fun y => u y*
      fderiv ℝ (fun z => fderiv ℝ φ z (v i)) (x-y) (v i)) μ := by
    simpa only [smul_eq_mul, Function.comp_def, Pi.sub_apply, id_eq] using hu.integrable_smul_right_of_hasCompactSupport
      ((hDD i).continuous.comp (continuous_const.sub continuous_id))
      (((hc.fderiv_apply ℝ (v i)).fderiv_apply ℝ (v i)).comp_homeomorph (Homeomorph.subLeft x))
  have he := heq θ ht htc
  have heθ (i : ι) (y : E) : fderiv ℝ θ y (v i) = -fderiv ℝ φ (x-y) (v i) :=
    ginibreLocalRegularity_reflected_fderiv φ hφ x y (v i)
  have heθθ (i : ι) (y : E) : fderiv ℝ (fun z => fderiv ℝ θ z (v i)) y (v i) =
      fderiv ℝ (fun z => fderiv ℝ φ z (v i)) (x-y) (v i) :=
    ginibreLocalRegularity_reflected_second φ hφ x y (v i)
  simp_rw [heθθ, heθ, mul_neg, integral_neg, Finset.sum_neg_distrib, sub_neg_eq_add] at he
  simp only [θ] at he
  have hs : (∫ y, u y*(∑ i, fderiv ℝ (fun z => fderiv ℝ φ z (v i)) (x-y) (v i)) ∂μ) =
      ∑ i, ∫ y, u y*fderiv ℝ (fun z => fderiv ℝ φ z (v i)) (x-y) (v i) ∂μ := by
    simp_rw [Finset.mul_sum]
    exact integral_finset_sum Finset.univ (fun i hi' => hi i)
  rw [hs] at he
  simp_rw [ginibreLocalRegularity_second_convolution_kernel μ u φ _ x hu hφ hc,
    ginibreLocalRegularity_fderiv_convolution_kernel μ _ φ _ x (hF _) hφ hc,
    convolution_lsmul_swap]
  convert he using 1
  · apply Finset.sum_congr rfl
    intro i hi'
    apply integral_congr_ae
    exact ae_of_all μ (fun y => mul_comm _ _)
  · congr 1
    · apply integral_congr_ae
      exact ae_of_all μ (fun y => mul_comm _ _)
    · apply Finset.sum_congr rfl
      intro i hi'
      apply integral_congr_ae
      exact ae_of_all μ (fun y => mul_comm _ _)

#print axioms ginibreLocalRegularity_mollified_elliptic_equation
end
end GinibrePoincare
