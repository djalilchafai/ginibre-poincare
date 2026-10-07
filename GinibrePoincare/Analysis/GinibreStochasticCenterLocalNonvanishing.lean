module

public import GinibrePoincare.Analysis.GinibreStochasticCenterSmallStopping
public import GinibrePoincare.Analysis.GinibreStochasticCenterLogVanishing

@[expose] public section

/-! Actual center nonvanishing up to every Hamiltonian localization, for
positive initial center. No non-hitting or Itô hypothesis is assumed. -/
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

theorem ginibreBrownian_center_local_zero_hitting_null
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z) (hcenter : 0 < ginibreCenterSquared n z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (R : ℝ) (hR : ginibreHamiltonian n z ≤ R) (T : ℝ≥0) :
    P {ω | ∃ t ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω,
      ginibreCenterSquared n (ginibreBrownianHamiltonianStoppedProcess n α z B R T t ω)=0}=0 := by
  classical
  let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
  let σ := ginibreBrownianHamiltonianBoundedStop n α z B R T
  let E := {ω | ∃ t ≤ σ ω, ginibreCenterSquared n (X t ω)=0}
  obtain ⟨D,hD,hDb,hθ,hθT,hHit⟩ := ginibreBrownian_center_small_stopping_exists (by omega) α z hz B P hB R hR T 0
  let u := fun t ω => D-ginibreCenterSquared n (X t ω)
  let θ := hittingBtwn u {x : ℝ | D ≤ ‖x‖} 0 T
  have hθ' : IsStoppingTime (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
      (fun ω => (θ ω : WithTop ℝ≥0)) := by simpa only [sub_zero] using hθ
  let τ := fun ω => min (θ ω) (σ ω)
  have hσ := ginibreBrownianHamiltonianBoundedStop_isStoppingTime (by omega) α z hz B P hB R hR T
  have hτ : IsStoppingTime (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
      (fun ω => (τ ω : WithTop ℝ≥0)) := by
    intro t
    have he : {ω | (τ ω : WithTop ℝ≥0) ≤ t} =
        {ω | (θ ω : WithTop ℝ≥0) ≤ t} ∪
          {ω | (ginibreBrownianHamiltonianBoundedStop n α z B R T ω : WithTop ℝ≥0) ≤ t} := by
      ext ω
      simp only [Set.mem_setOf_eq,Set.mem_union,WithTop.coe_le_coe]
      change min (θ ω) (σ ω) ≤ t ↔ θ ω ≤ t ∨ σ ω ≤ t
      exact min_le_iff
    rw [he]
    exact (hθ'.measurableSet_le t).union (hσ.measurableSet_le t)

  have hτσ : ∀ ω, τ ω ≤ σ ω := fun ω => min_le_right _ _
  have hSubset : E ⊆ {ω | ginibreCenterSquared n (X (τ ω) ω) ≤ 0} := by
    intro ω hω
    obtain ⟨t,ht,he⟩ := hω
    have hh := hHit ω ⟨t,ht,he.le⟩
    simp only [sub_zero] at hh
    have hτe : τ ω=θ ω := min_eq_left hh.1
    change ginibreCenterSquared n (X (τ ω) ω) ≤ 0
    rw [hτe]
    exact hh.2
  obtain ⟨C,hC,hProb⟩ := ginibreBrownian_center_small_stopped_probability hn α z hz B P hB hind R hR T
  have hp : P.real E=0 := ginibre_probability_zero_of_log_barriers (measureReal_nonneg) hC hcenter
    (fun ε hε => by
      have h := hProb 0 le_rfl hC ε hε τ hτ hτσ
      simp only [zero_add] at h
      exact (measureReal_mono (μ := P) hSubset).trans h)
  exact (measureReal_eq_zero_iff (μ := P)).mp hp
end
end GinibrePoincare
