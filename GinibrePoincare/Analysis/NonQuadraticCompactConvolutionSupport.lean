module

public import GinibrePoincare.Analysis.NonQuadraticSeparatedConvolution
public import GinibrePoincare.Analysis.NonQuadraticLpMultiplier

@[expose] public section

/-! # Actual common compact support for separated convolution -/
open MeasureTheory Filter
open scoped Topology Pointwise ENNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem separatedCompactConvolution_eq_zero_of_not_mem
    (f : ℂ × ℂ → ℂ) (φ ψ : ContDiffBump (0 : ℂ)) (R : ℝ)
    (hR : max φ.rOut ψ.rOut ≤ R) (x : ℂ × ℂ)
    (hx : x ∉ tsupport f + Metric.closedBall (0 : ℂ × ℂ) R) :
    (∫ a, f a * (separatedPlanarBump φ ψ (x-a) : ℂ)
      ∂((volume : Measure ℂ).prod (volume : Measure ℂ))) = 0 := by
  apply integral_eq_zero_of_ae
  apply Eventually.of_forall
  intro a
  by_cases ha : f a = 0
  · simp only [ha, zero_mul, Pi.zero_apply]
  by_cases hk : separatedPlanarBump φ ψ (x-a) = 0
  · simp only [hk, Complex.ofReal_zero, mul_zero, Pi.zero_apply]
  exfalso
  apply hx
  exact ⟨a, subset_closure ha, x-a,
    ((separatedPlanarBump_support_ball φ ψ (x-a) hk).le.trans hR), by abel⟩

/-- Every continuous weight has a genuine bounded multiplication operator
on a fixed compact region of the whole product-plane L² space. -/
theorem exists_compactProductL2WeightMultiplier
    (w : ℂ × ℂ → ℂ) (hw : Continuous w) (S : Set (ℂ × ℂ)) (hS : IsCompact S) :
    ∃ T : Lp ℂ 2 ((volume : Measure ℂ).prod (volume : Measure ℂ)) →L[ℂ]
      Lp ℂ 2 ((volume : Measure ℂ).prod (volume : Measure ℂ)),
      ∀ u, (T u : ℂ × ℂ → ℂ) =ᵐ[(volume : Measure ℂ).prod (volume : Measure ℂ)]
        (fun x => (S.indicator w) x * u x) := by
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hw.continuousOn
  let b := S.indicator w
  have hb : AEStronglyMeasurable b ((volume : Measure ℂ).prod (volume : Measure ℂ)) :=
    hw.aestronglyMeasurable.indicator hS.measurableSet
  have hbn (x : ℂ × ℂ) : ‖b x‖ ≤ max C 0 := by
    by_cases hx : x ∈ S
    · simpa only [b, Set.indicator_of_mem hx] using (hC x hx).trans (le_max_left _ _)
    · simpa only [b, Set.indicator_of_notMem hx, norm_zero] using (le_max_right C 0)
  exact ⟨boundedComplexL2Multiplier b hb (max C 0) hbn,
    boundedComplexL2Multiplier_coeFn b hb (max C 0) hbn⟩
end
end GinibrePoincare
