module

public import GinibrePoincare.Analysis.GinibreStochasticNoncollision
public import GinibrePoincare.Analysis.GinibreHamiltonianPathUniqueness

@[expose] public section

/-! Actual global pathwise uniqueness for the original singular Brownian equation. -/
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000

theorem ginibreBrownianMaximalProcess_global_pathwise_unique
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (Y : ℝ → Ω → Configuration n)
    (hY : ∀ᵐ ω ∂P, Continuous (fun t => Y t ω) ∧ Y 0 ω=z ∧
      (∀ t : ℝ, 0 ≤ t → CollisionFree (Y t ω)) ∧
      IsGinibreDrivenPath n α (ginibreConfigurationBrownianNoise n B α ω) (fun t => Y t ω)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Y t ω=ginibreBrownianMaximalProcess n α z B t.toNNReal ω := by
  have hGlobal := (ginibreBrownianMaximalProcess_global_original_solution hn α z hz B P hB hind).2
  filter_upwards [hGlobal,hY] with ω hX hY
  intro t ht
  let X := fun s : ℝ => ginibreBrownianMaximalProcess n α z B s.toNNReal ω
  have hinit : X 0=z := by simpa [X] using hX.2.1
  have hEqX (s : ℝ) (hs : s ∈ Icc 0 t) : X s=z+ginibreConfigurationBrownianNoise n B α ω s+
      ∫ u in (0 : ℝ)..s, ginibreLangevinDrift n α (X u) := by
    have h := hX.2.2.2.2 s hs.1
    change X s=X 0+ginibreConfigurationBrownianNoise n B α ω s+
      ∫ u in (0 : ℝ)..s, ginibreLangevinDrift n α (X u) at h
    rw [hinit] at h
    exact h
  have hEqY (s : ℝ) (hs : s ∈ Icc 0 t) : Y s ω=z+ginibreConfigurationBrownianNoise n B α ω s+
      ∫ u in (0 : ℝ)..s, ginibreLangevinDrift n α (Y u ω) := by
    have h := hY.2.2.2.2 s hs.1
    dsimp only at h
    rw [hY.2.1] at h
    exact h
  exact ginibreDrivenPath_finite_interval_unique n α z (ginibreConfigurationBrownianNoise n B α ω)
    (fun s => Y s ω) X t ht hY.1.continuousOn hX.1.continuousOn
    (fun s hs => hY.2.2.1 s hs.1) (fun s hs => hX.2.2.1 s hs.1) hEqY hEqX ⟨ht,le_rfl⟩
end
end GinibrePoincare
