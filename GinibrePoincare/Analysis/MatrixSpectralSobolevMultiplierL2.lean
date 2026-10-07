module

public import GinibrePoincare.Analysis.GinibreWeakSobolevMultipliers

@[expose] public section

/-! # Genuine L² Leibniz pairs under arbitrary weighted laws -/
open MeasureTheory Filter
open scoped Topology ContDiff ENNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 400000

theorem configuration_weak_multiplier_memLp (n : ℕ)
    (μ : Measure (Configuration n)) (u : Configuration n → ℝ)
    (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (hu : MemLp u 2 μ) (hg : MemLp g 2 μ)
    (χ : Configuration n → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    MemLp (fun z => χ z * u z) 2 μ ∧
    MemLp (fun z => χ z • g z + u z • ginibreEuclideanGradient χ z)
      2 μ := by
  obtain ⟨A, hA⟩ := hχ.continuous.bounded_above_of_compact_support hc
  obtain ⟨B, hB⟩ := (continuous_ginibreEuclideanGradient χ hχ).bounded_above_of_compact_support
    (compactSupport_ginibreEuclideanGradient χ hc)
  have hA0 : 0 ≤ A := (norm_nonneg (χ 0)).trans (hA 0)
  have hB0 : 0 ≤ B := (norm_nonneg (ginibreEuclideanGradient χ 0)).trans (hB 0)
  have hv : MemLp (fun z => χ z * u z) 2 μ := by
    apply (hu.const_mul A).of_le
      (hχ.continuous.aestronglyMeasurable.mul hu.aestronglyMeasurable)
    exact ae_of_all _ (fun z => by
      change ‖χ z * u z‖ ≤ ‖A * u z‖
      rw [norm_mul, norm_mul, Real.norm_eq_abs A, abs_of_nonneg hA0]
      exact mul_le_mul_of_nonneg_right (hA z) (norm_nonneg (u z)))
  have hvG : MemLp (fun z => χ z • g z) 2 μ := by
    apply (hg.const_smul A).of_le
      (hχ.continuous.aestronglyMeasurable.smul hg.aestronglyMeasurable)
    exact ae_of_all _ (fun z => by
      change ‖χ z • g z‖ ≤ ‖A • g z‖
      rw [norm_smul, norm_smul, Real.norm_eq_abs A, abs_of_nonneg hA0]
      exact mul_le_mul_of_nonneg_right (hA z) (norm_nonneg (g z)))
  have hdG : MemLp (fun z => u z • ginibreEuclideanGradient χ z) 2 μ := by
    apply (hu.const_mul B).of_le
      (hu.aestronglyMeasurable.smul (continuous_ginibreEuclideanGradient χ hχ).aestronglyMeasurable)
    exact ae_of_all _ (fun z => by
      change ‖u z • ginibreEuclideanGradient χ z‖ ≤ ‖B * u z‖
      rw [norm_smul, norm_mul, Real.norm_eq_abs B, abs_of_nonneg hB0]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (hB z) (norm_nonneg (u z)))
  exact ⟨hv, hvG.add hdG⟩


end
end GinibrePoincare
