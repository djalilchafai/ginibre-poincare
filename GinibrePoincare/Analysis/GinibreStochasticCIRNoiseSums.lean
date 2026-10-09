module

public import GinibrePoincare.Analysis.GinibreStochasticCIRNoiseCoefficient
public import GinibrePoincare.Analysis.GinibreStochasticCompactGradientIntegral

@[expose] public section

/-! The actual finite configuration-noise sums already have the precise CIR
amplitude and actual radial-unit innovation, before any stochastic limit. -/
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000

theorem ginibreConfigurationBrownianGradientSum_radius {Ω : Type*} {n : ℕ}
    (hn : 2 ≤ n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (α : ℝ) (hα : 0 ≤ α) (X : ℝ≥0 → Ω → Configuration n)
    (hX : ∀ s ω, CollisionFree (X s ω)) (e : EuclideanSpace ℝ (Fin n × Fin 2))
    (T : ℝ≥0) (k : ℕ) (ω : Ω) :
    ginibreConfigurationBrownianGradientSum n B α X pairwiseRadius T k ω =
      ∑ i, brownianUniformLeftSum (B i)
        (fun s ω => Real.sqrt ((8*α/(n : ℝ))*pairwiseRadius (X s ω))*
          ginibreRecenteredRadialDirection n e (X s ω) i) T (k+1) ω := by
  classical
  rw [ginibreConfigurationBrownianGradientSum_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  unfold brownianUniformLeftSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← mul_assoc, ginibreCIR_noise_coordinate hn α hα _ (hX _ ω) e i]

end
end GinibrePoincare
