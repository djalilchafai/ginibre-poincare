module

public import GinibrePoincare.Analysis.GinibreStochasticSquareRootRadius
public import GinibrePoincare.Analysis.GinibreStochasticCIRFullNoiseSums

@[expose] public section

/-! Exact finite Lamperti noise sums equal a constant times the actual
original global radial-unit innovations before the actual Hamiltonian stop. -/
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1500000

theorem ginibreConfigurationBrownianGradientSum_squareRootRadius_full_direction
    {Ω : Type*} {n : ℕ} (hn : 2 ≤ n) (α : ℝ) (hα : 0 ≤ α)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (R : ℝ) (hR : ginibreHamiltonian n z ≤ R) (T : ℝ≥0)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (t : ℝ≥0) (k : ℕ) (ω : Ω)
    (ht : t ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω) :
    let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
    ginibreConfigurationBrownianGradientSum n B α X ginibreSquareRootRadius t k ω =
      Real.sqrt (2*α/(n : ℝ))*∑ i, brownianUniformLeftSum (B i)
        (fun s ω => ginibreRecenteredRadialDirection n e (ginibreBrownianMaximalProcess n α z B s ω) i)
        t (k+1) ω := by
  classical
  dsimp only
  rw [ginibreConfigurationBrownianGradientSum_eq, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  unfold brownianUniformLeftSum
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  dsimp only
  have hjT : itoUniformNNTime t (k+1) j ≤ t :=
    itoUniformNNTime_le_end t (k+1) j (Nat.succ_pos k) (Finset.mem_range.mp hj).le
  have he : ginibreBrownianHamiltonianStoppedProcess n α z B R T (itoUniformNNTime t (k+1) j) ω =
      ginibreBrownianMaximalProcess n α z B (itoUniformNNTime t (k+1) j) ω := by
    change ginibreBrownianMaximalProcess n α z B
      (min (itoUniformNNTime t (k+1) j) (ginibreBrownianHamiltonianBoundedStop n α z B R T ω)) ω = _
    rw [min_eq_left (hjT.trans ht)]
  have hCF := (ginibreBrownianHamiltonianStoppedProcess_range (by omega) α z hz B R hR T
    (itoUniformNNTime t (k+1) j) ω).1
  rw [← mul_assoc, ginibre_squareRootRadius_noise_coordinate hn α hα _ hCF e i, he, mul_assoc]
end
end GinibrePoincare
