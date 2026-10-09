module

public import GinibrePoincare.Analysis.GinibreStochasticCenterCIRNoiseCoefficient
public import GinibrePoincare.Analysis.GinibreStochasticCompactGradientIntegral

@[expose] public section

/-! The actual finite configuration-noise sums already have the precise CIR
amplitude and actual radial-unit innovation, before any stochastic limit. -/
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000

theorem ginibreCenterCIR_noise_coordinate_all {n : ℕ} (hn : 0 < n)
    (α : ℝ) (hα : 0 ≤ α) (z : Configuration n)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (i : Fin n × Fin 2) :
    Real.sqrt (2*α/(n : ℝ)^2)*fderiv ℝ (ginibreCenterSquared n) z (ginibreCoordinateDirection i) =
      Real.sqrt ((8*α/(n : ℝ))*ginibreCenterSquared n z)*ginibreCenterRadialDirection n e z i := by
  by_cases hz : ginibreCenterSquared n z=0
  · have hs : coordinateSum z=0 := Complex.normSq_eq_zero.mp hz
    simp [hz, ginibre_fderiv_centerSquared, hs]
  · exact ginibreCenterCIR_noise_coordinate hn α hα z hz e i

theorem ginibreConfigurationBrownianGradientSum_centerSquared {Ω : Type*} {n : ℕ}
    (hn : 2 ≤ n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (α : ℝ) (hα : 0 ≤ α) (X : ℝ≥0 → Ω → Configuration n)
    (hX : ∀ s ω, CollisionFree (X s ω)) (e : EuclideanSpace ℝ (Fin n × Fin 2))
    (T : ℝ≥0) (k : ℕ) (ω : Ω) :
    ginibreConfigurationBrownianGradientSum n B α X (ginibreCenterSquared n) T k ω =
      ∑ i, brownianUniformLeftSum (B i)
        (fun s ω => Real.sqrt ((8*α/(n : ℝ))*(ginibreCenterSquared n) (X s ω))*
          ginibreCenterRadialDirection n e (X s ω) i) T (k+1) ω := by
  classical
  rw [ginibreConfigurationBrownianGradientSum_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  unfold brownianUniformLeftSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← mul_assoc, ginibreCenterCIR_noise_coordinate_all (by omega) α hα _ e i]

end
end GinibrePoincare
