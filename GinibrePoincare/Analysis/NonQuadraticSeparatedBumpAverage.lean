module

public import GinibrePoincare.Analysis.NonQuadraticSeparatedBump

@[expose] public section

/-! # Actual separated convolution is a strong L² approximate identity -/
open MeasureTheory Filter
open scoped Topology ENNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

def separatedL2BumpAverage (φ ψ : ContDiffBump (0 : ℂ))
    (u : Lp W 2 (volume : Measure (ℂ × ℂ))) : Lp W 2 (volume : Measure (ℂ × ℂ)) :=
  ∫ y, separatedPlanarBump φ ψ y • productPlaneL2Translate y u

theorem separatedPlanarBump_integrable (φ ψ : ContDiffBump (0 : ℂ)) :
    Integrable (separatedPlanarBump φ ψ) (volume : Measure (ℂ × ℂ)) :=
  (separatedPlanarBump_continuous φ ψ).integrable_of_hasCompactSupport
    (separatedPlanarBump_compact φ ψ)

theorem integrable_separatedL2BumpIntegrand (φ ψ : ContDiffBump (0 : ℂ))
    (u : Lp W 2 (volume : Measure (ℂ × ℂ))) :
    Integrable (fun y => separatedPlanarBump φ ψ y • productPlaneL2Translate y u) :=
  ((separatedPlanarBump_continuous φ ψ).smul (continuous_productPlaneL2Translate u)).integrable_of_hasCompactSupport (separatedPlanarBump_compact φ ψ).smul_right

theorem separatedL2BumpAverage_error_le (φ ψ : ContDiffBump (0 : ℂ))
    (u : Lp W 2 (volume : Measure (ℂ × ℂ))) (ε : ℝ)
    (he : ∀ y ∈ Function.support (separatedPlanarBump φ ψ),
      ‖productPlaneL2Translate y u - u‖ ≤ ε) :
    ‖separatedL2BumpAverage φ ψ u - u‖ ≤ ε := by
  have hconst : Integrable (fun y => separatedPlanarBump φ ψ y • u) :=
    (separatedPlanarBump_integrable φ ψ).smul_const u
  have hint := integrable_separatedL2BumpIntegrand φ ψ u
  have hmass : (∫ y, separatedPlanarBump φ ψ y • u) = u := by
    rw [integral_smul_const]
    change (∫ y, separatedPlanarBump φ ψ y ∂((volume : Measure ℂ).prod volume)) • u = u
    rw [separatedPlanarBump_integral, one_smul]
  have heq : separatedL2BumpAverage φ ψ u - u =
      ∫ y, separatedPlanarBump φ ψ y • (productPlaneL2Translate y u - u) := by
    unfold separatedL2BumpAverage
    calc
      _ = (∫ y, separatedPlanarBump φ ψ y • productPlaneL2Translate y u) -
          ∫ y, separatedPlanarBump φ ψ y • u := by rw [hmass]
      _ = ∫ y, (separatedPlanarBump φ ψ y • productPlaneL2Translate y u -
          separatedPlanarBump φ ψ y • u) := (integral_sub hint hconst).symm
      _ = _ := integral_congr_ae (Eventually.of_forall (fun y => (smul_sub _ _ _).symm))
  rw [heq]
  have hnorm : ‖∫ y, separatedPlanarBump φ ψ y • (productPlaneL2Translate y u - u)‖ ≤
      ∫ y, separatedPlanarBump φ ψ y * ε := by
    apply norm_integral_le_of_norm_le ((separatedPlanarBump_integrable φ ψ).mul_const ε)
    exact Eventually.of_forall (fun y => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (separatedPlanarBump_nonneg φ ψ y)]
      by_cases hy : separatedPlanarBump φ ψ y = 0
      · simp [hy]
      · exact mul_le_mul_of_nonneg_left (he y hy) (separatedPlanarBump_nonneg φ ψ y))
  have hi : (∫ y, separatedPlanarBump φ ψ y ∂(volume : Measure (ℂ × ℂ))) = 1 :=
    separatedPlanarBump_integral φ ψ
  simpa only [integral_mul_const, hi, one_mul] using hnorm

/-- Actual product bump convolution converges strongly on the whole vector-
valued product-plane L² space, not only on separated functions. -/
theorem separatedL2BumpAverage_tendsto (φ ψ : ℕ → ContDiffBump (0 : ℂ))
    (hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0))
    (hψ : Tendsto (fun m => (ψ m).rOut) atTop (𝓝 0))
    (u : Lp W 2 (volume : Measure (ℂ × ℂ))) :
    Tendsto (fun m => separatedL2BumpAverage (φ m) (ψ m) u) atTop (𝓝 u) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨δ, hδ, ht⟩ := Metric.continuousAt_iff.mp
    (continuous_productPlaneL2Translate u).continuousAt (ε / 2) (half_pos hε)
  have hr : Tendsto (fun m => max (φ m).rOut (ψ m).rOut) atTop (𝓝 0) := by
    simpa only [max_self] using hφ.max hψ
  obtain ⟨M, hM⟩ := eventually_atTop.mp ((tendsto_order.mp hr).2 δ hδ)
  refine ⟨M, fun m hm => ?_⟩
  rw [dist_eq_norm]
  apply (separatedL2BumpAverage_error_le (φ m) (ψ m) u (ε / 2) ?_).trans_lt (half_lt_self hε)
  intro y hy
  have hd : dist y 0 < δ := (separatedPlanarBump_support_ball (φ m) (ψ m) y hy).trans (hM m hm)
  have he := ht hd
  simpa only [productPlaneL2Translate_zero, dist_eq_norm] using he.le
end
end GinibrePoincare
