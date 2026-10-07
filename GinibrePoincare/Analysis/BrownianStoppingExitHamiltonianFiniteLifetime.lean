module

public import GinibrePoincare.Analysis.BrownianStoppingExitHamiltonianStoppedPath

@[expose] public section

/-! Every finite-lifetime event reaches each high Hamiltonian level before the bounded stop. -/
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem ginibreBrownianMaximalLifetime_le_hamiltonian_level {Ω : Type*} {n : ℕ} (hn : 0 < n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (R : ℝ) (hR : ginibreHamiltonian n z ≤ R)
    (T : ℝ≥0) (ω : Ω) (hDeath : ginibreBrownianMaximalLifetime n α z B ω ≤ (T : ℝ≥0∞)) :
    ginibreBrownianHamiltonianFirstLevel n α z B R ω ≤ (T : ℝ≥0∞) :=
  (ginibreDrivenHamiltonianFirstLevel_le_iff_lifetime hn α
    (ginibreBrownianFullContinuousNoise n B α ω).val
    (ginibreBrownianFullContinuousNoise n B α ω).val.continuous
    (ginibreBrownianFullContinuousNoise n B α ω).property z hz R hR T).mpr (Or.inl hDeath)

 theorem ginibreBrownianMaximalLifetime_le_stopped_hamiltonian_eq {Ω : Type*} {n : ℕ} (hn : 0 < n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (R : ℝ) (hR : ginibreHamiltonian n z ≤ R)
    (T : ℝ≥0) (ω : Ω) (hDeath : ginibreBrownianMaximalLifetime n α z B ω ≤ (T : ℝ≥0∞)) :
    ginibreHamiltonian n (ginibreBrownianHamiltonianStoppedProcess n α z B R T T ω) = R := by
  have hs := ginibreDrivenHamiltonianBoundedStop_le n α
    (ginibreBrownianFullContinuousNoise n B α ω).val z R T
  change ginibreHamiltonian n (ginibreDrivenMaximalValue n α
    (ginibreBrownianFullContinuousNoise n B α ω).val z
    (min T (ginibreDrivenHamiltonianBoundedStop n α
      (ginibreBrownianFullContinuousNoise n B α ω).val z R T))) = R
  rw [min_eq_right hs]
  exact ginibreDrivenHamiltonianBoundedStop_hamiltonian_eq hn α
    (ginibreBrownianFullContinuousNoise n B α ω).val
    (ginibreBrownianFullContinuousNoise n B α ω).val.continuous
    (ginibreBrownianFullContinuousNoise n B α ω).property z hz R hR T
    (ginibreBrownianMaximalLifetime_le_hamiltonian_level hn α z hz B R hR T ω hDeath)

end
end GinibrePoincare
