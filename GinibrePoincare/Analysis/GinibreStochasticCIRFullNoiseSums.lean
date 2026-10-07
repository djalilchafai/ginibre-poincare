module

public import GinibrePoincare.Analysis.GinibreStochasticCIRCoefficientProcess

@[expose] public section

/-! Before the actual Hamiltonian stopping time, finite CIR noise sums use
the radial direction of the original global solution itself. -/
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000

theorem ginibreConfigurationBrownianGradientSum_radius_full_direction
    {Ω : Type*} {n : ℕ} (hn : 2 ≤ n) (α : ℝ) (hα : 0 ≤ α)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (R : ℝ) (hR : ginibreHamiltonian n z ≤ R) (T : ℝ≥0)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (t : ℝ≥0) (k : ℕ) (ω : Ω)
    (ht : t ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω) :
    let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
    ginibreConfigurationBrownianGradientSum n B α X pairwiseRadius t k ω =
      ∑ i, brownianUniformLeftSum (B i)
        (fun s ω => Real.sqrt ((8*α/(n : ℝ))*pairwiseRadius (X s ω))*
          ginibreRecenteredRadialDirection n e (ginibreBrownianMaximalProcess n α z B s ω) i)
        t (k+1) ω := by
  classical
  dsimp only
  rw [ginibreConfigurationBrownianGradientSum_radius hn B α hα _
    (fun s ω => (ginibreBrownianHamiltonianStoppedProcess_range (by omega) α z hz B R hR T s ω).1) e]
  apply Finset.sum_congr rfl
  intro i hi
  unfold brownianUniformLeftSum
  apply Finset.sum_congr rfl
  intro j hj
  have hjT : itoUniformNNTime t (k+1) j ≤ t :=
    itoUniformNNTime_le_end t (k+1) j (Nat.succ_pos k) (Finset.mem_range.mp hj).le
  have he : ginibreBrownianHamiltonianStoppedProcess n α z B R T (itoUniformNNTime t (k+1) j) ω =
      ginibreBrownianMaximalProcess n α z B (itoUniformNNTime t (k+1) j) ω := by
    change ginibreBrownianMaximalProcess n α z B
      (min (itoUniformNNTime t (k+1) j) (ginibreBrownianHamiltonianBoundedStop n α z B R T ω)) ω = _
    rw [min_eq_left (hjT.trans ht)]
  dsimp only
  rw [he]

end
end GinibrePoincare
