module

public import GinibrePoincare.Analysis.GinibreDrivenPathLocalStability

@[expose] public section

/-! Actual singular Ginibre drift admits local uniform dependence on the driving noise. -/
open MeasureTheory Set Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000

theorem ginibreDrivenPath_local_noise_stability (n : ℕ) (α : ℝ) (z : Configuration n)
    (hz : CollisionFree z) : ∃ L : ℝ≥0, ∃ U ∈ nhds z,
    ∀ (N M X Y : ℝ → Configuration n) (T δ : ℝ), 0 ≤ T → 0 ≤ δ →
      ContinuousOn X (Icc 0 T) → ContinuousOn Y (Icc 0 T) →
      (∀ t ∈ Icc 0 T, X t ∈ U) → (∀ t ∈ Icc 0 T, Y t ∈ U) →
      (∀ t ∈ Icc 0 T, X t = z+N t+∫ s in (0 : ℝ)..t, ginibreLangevinDrift n α (X s)) →
      (∀ t ∈ Icc 0 T, Y t = z+M t+∫ s in (0 : ℝ)..t, ginibreLangevinDrift n α (Y s)) →
      (∀ t ∈ Icc 0 T, ‖N t-M t‖ ≤ δ) →
      ∀ t ∈ Icc 0 T, ‖X t-Y t‖ ≤ δ*Real.exp ((L : ℝ)*T) := by
  obtain ⟨K,U,hU,hb⟩ := ginibreLangevinDrift_local_lipschitz n α z hz
  obtain ⟨g,hg,heq⟩ := hb.extend_finite_dimension
  refine ⟨lipschitzExtensionConstant (Configuration n)*K, U,hU, ?_⟩
  intro N M X Y T δ hT hδ hX hY hXU hYU hEqX hEqY hNoise
  have hEqXg (t : ℝ) (ht : t ∈ Icc 0 T) : X t = z+N t+∫ s in (0 : ℝ)..t, g (X s) := by
    rw [hEqX t ht]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only
    rw [uIcc_of_le ht.1] at hs
    exact heq (hXU s ⟨hs.1,hs.2.trans ht.2⟩)
  have hEqYg (t : ℝ) (ht : t ∈ Icc 0 T) : Y t = z+M t+∫ s in (0 : ℝ)..t, g (Y s) := by
    rw [hEqY t ht]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    dsimp only
    rw [uIcc_of_le ht.1] at hs
    exact heq (hYU s ⟨hs.1,hs.2.trans ht.2⟩)
  exact drivenVolterra_lipschitz_stability_on g _ hg z N M X Y T δ hT hδ hX hY hEqXg hEqYg hNoise

end
end GinibrePoincare
