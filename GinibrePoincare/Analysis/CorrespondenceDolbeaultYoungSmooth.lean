module
public import GinibrePoincare.Analysis.CorrespondenceDolbeaultYoungSmoothPairing

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The actual Bochner coordinate operator has its literal smooth convolution
representative; the kernel only needs L¹, not continuity or square integrability. -/
theorem dolbeaultCoordinateConvolution_pointwise_ae {n : ℕ} (j : Fin n)
    (k : ℂ → ℂ) (hk : Integrable k volume)
    (f : Configuration n → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    (dolbeaultCoordinateConvolution j k ((hf.continuous.memLp_of_hasCompactSupport
      (p := 2) (μ := volume) hc).toLp f) : Configuration n → ℂ) =ᵐ[volume]
      dolbeaultCoordinateConvolutionPointwise j k f := by
  let hm := hf.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hc
  let u : dolbeaultOrdinaryL2 n := hm.toLp f
  have hfi : Integrable f volume := hf.continuous.integrable_of_hasCompactSupport hc
  have hloc : LocallyIntegrable (dolbeaultCoordinateConvolutionPointwise j k f) volume :=
    (dolbeaultCoordinateConvolutionPointwise_smooth j k hk.locallyIntegrable f hf hc).continuous.locallyIntegrable
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (dolbeaultCoordinateConvolution j k u)).locallyIntegrable (by norm_num)) hloc
  intro θ hθ hθc
  let Θ : Configuration n → ℂ := fun x => (θ x : ℂ)
  have hΘ : Continuous Θ := Complex.continuous_ofReal.comp hθ.continuous
  have hcΘ : HasCompactSupport Θ := hθc.comp_left Complex.ofReal_zero
  have he (a : ℂ) : (∫ x : Configuration n, Θ x*u (x-Pi.single j a)) =
      ∫ x : Configuration n, Θ x*f (x-Pi.single j a) := by
    apply integral_congr_ae
    have h := (eventually_add_right_iff (volume : Measure (Configuration n))
      (-(Pi.single j a : Configuration n))).mpr hm.coeFn_toLp
    filter_upwards [h] with x hx
    simpa only [sub_eq_add_neg] using congrArg (fun t => Θ x*t) hx
  calc
    _ = ∫ x : Configuration n, Θ x*(dolbeaultCoordinateConvolution j k u) x := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by simp [Θ, Complex.real_smul])
    _ = ∫ y : ℂ, k y*(∫ x : Configuration n, Θ x*u (x-Pi.single j y)) :=
      dolbeaultCoordinateConvolution_compact_test j k hk u Θ hΘ hcΘ
    _ = ∫ y : ℂ, k y*(∫ x : Configuration n, Θ x*f (x-Pi.single j y)) := by simp_rw [he]
    _ = ∫ x : Configuration n, Θ x*dolbeaultCoordinateConvolutionPointwise j k f x :=
      (dolbeaultCoordinatePointwise_compact_test j k hk f hf.continuous hfi Θ hΘ hcΘ).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by simp [Θ, Complex.real_smul])

/-- Literal smooth compact representative of the truncated singular coordinate solver. -/
theorem dolbeaultCauchyGreenL2_smooth_compact_representative {n : ℕ} (j : Fin n)
    (R : ℝ) (f : Configuration n → ℂ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (dolbeaultCoordinateConvolutionPointwise j (dolbeaultTruncatedCauchyGreen R) f) ∧
    HasCompactSupport (dolbeaultCoordinateConvolutionPointwise j (dolbeaultTruncatedCauchyGreen R) f) ∧
    (dolbeaultCauchyGreenL2 j R ((hf.continuous.memLp_of_hasCompactSupport
      (p := 2) (μ := volume) hc).toLp f) : Configuration n → ℂ) =ᵐ[volume]
      dolbeaultCoordinateConvolutionPointwise j (dolbeaultTruncatedCauchyGreen R) f := by
  have hk : HasCompactSupport (dolbeaultTruncatedCauchyGreen R) := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) R)
    intro x hx
    by_contra h
    exact hx (Set.indicator_of_notMem h _)
  exact ⟨dolbeaultCoordinateConvolutionPointwise_smooth j _
    (dolbeaultTruncatedCauchyGreen_integrable R).locallyIntegrable f hf hc,
    dolbeaultCoordinateConvolutionPointwise_compact j _ hk f hc,
    dolbeaultCoordinateConvolution_pointwise_ae j _ (dolbeaultTruncatedCauchyGreen_integrable R) f hf hc⟩

#print axioms dolbeaultCoordinateConvolution_pointwise_ae
#print axioms dolbeaultCauchyGreenL2_smooth_compact_representative
end
end GinibrePoincare
