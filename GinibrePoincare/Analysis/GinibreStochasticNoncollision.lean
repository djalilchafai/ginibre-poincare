module

public import GinibrePoincare.Analysis.GinibreStochasticHamiltonianIto
public import GinibrePoincare.Analysis.BrownianStoppingExitHamiltonianGlobalSolution

@[expose] public section

/-! Global noncollision and nonexplosion of the actual original Ginibre Brownian SDE.
The Hamiltonian martingales and their Itô identities are constructed internally. -/
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000

theorem ginibreBrownianMaximalLifetime_top_ae
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    ∀ᵐ ω ∂P, ginibreBrownianMaximalLifetime n α z B ω=⊤ := by
  apply ginibreBrownianMaximalLifetime_top_ae_of_stopped_martingales hn α α.coe_nonneg z hz B P hB
  intro T R hR
  obtain ⟨J,hJM,hJC,hJL,hJ0,hLocal,hTerminal⟩ :=
    ginibreBrownianHamiltonian_continuous_ito_martingale_exists hn α z hz B P hB hind R hR.le T
  exact ⟨J,hJM,Filter.Eventually.of_forall hJC,hJ0,hTerminal⟩

theorem ginibreBrownianMaximalProcess_global_original_solution
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
      (ginibreBrownianMaximalProcess n α z B) ∧
    ∀ᵐ ω ∂P,
      Continuous (fun t : ℝ => ginibreBrownianMaximalProcess n α z B t.toNNReal ω) ∧
      ginibreBrownianMaximalProcess n α z B 0 ω=z ∧
      (∀ t : ℝ, 0 ≤ t → CollisionFree (ginibreBrownianMaximalProcess n α z B t.toNNReal ω)) ∧
      IsGinibreDrivenPath n α (ginibreConfigurationBrownianNoise n B α ω)
        (fun t : ℝ => ginibreBrownianMaximalProcess n α z B t.toNNReal ω) := by
  refine ⟨ginibreBrownianMaximalProcess_stronglyAdapted hn α z B P hB,?_⟩
  apply ginibreBrownianMaximalProcess_global_original_solution_ae_of_stopped_martingales
    hn α α.coe_nonneg z hz B P hB
  intro T R hR
  obtain ⟨J,hJM,hJC,hJL,hJ0,hLocal,hTerminal⟩ :=
    ginibreBrownianHamiltonian_continuous_ito_martingale_exists hn α z hz B P hB hind R hR.le T
  exact ⟨J,hJM,Filter.Eventually.of_forall hJC,hJ0,hTerminal⟩
end
end GinibrePoincare
