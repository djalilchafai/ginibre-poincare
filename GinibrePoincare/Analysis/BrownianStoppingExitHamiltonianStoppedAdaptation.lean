module

public import GinibrePoincare.Analysis.BrownianStoppingExitHamiltonianStoppedEquation
public import GinibrePoincare.Analysis.BrownianStoppingExitCountableEvaluation
public import GinibrePoincare.Analysis.GinibreHamiltonianMaximalTimeContinuity

@[expose] public section

/-! Genuine strong adaptation of the compact localized maximal path, proved by countable
upper stopping approximations and continuity strictly before its lifetime. -/
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 theorem ginibreBrownianHamiltonianStoppedProcess_stronglyAdapted {Ω : Type*}
    [mAmbient : MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (R : ℝ) (hR : ginibreHamiltonian n z ≤ R)
    (T : ℝ≥0) :
    StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
      (ginibreBrownianHamiltonianStoppedProcess n α z B R T) := by
  let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
  let σ := ginibreBrownianHamiltonianBoundedStop n α z B R T
  have hσ := ginibreBrownianHamiltonianBoundedStop_isStoppingTime hn α z hz B P hB R hR T
  have hu := ginibreBrownianMaximalProcess_stronglyAdapted hn α z B P hB
  intro s
  have hMeas (m : ℕ) : @StronglyMeasurable Ω (Configuration n) _ (F s)
      (fun ω => ginibreBrownianMaximalProcess n α z B (min s (stoppingUpperGrid m (σ ω))) ω) :=
    (adapted_capped_upper_grid_evaluation_measurable F _ hu.adapted σ hσ m s).stronglyMeasurable
  apply stronglyMeasurable_of_tendsto atTop hMeas
  rw [tendsto_pi_nhds]
  intro ω
  have hsσ := ginibreDrivenHamiltonianBoundedStop_lt_lifetime hn α
    (ginibreBrownianFullContinuousNoise n B α ω).val
    (ginibreBrownianFullContinuousNoise n B α ω).val.continuous
    (ginibreBrownianFullContinuousNoise n B α ω).property z hz R hR T
  have hs : ((min s (σ ω) : ℝ≥0) : ℝ≥0∞) <
      ginibreDrivenMaximalLifetime n α (ginibreBrownianFullContinuousNoise n B α ω).val z :=
    (ENNReal.coe_le_coe.mpr (min_le_right s (σ ω))).trans_lt hsσ
  have hc := ginibreDrivenMaximalValue_continuousAt_time (min s (σ ω)) hs
  exact hc.tendsto.comp (tendsto_const_nhds.min (stoppingUpperGrid_tendsto (σ ω)))

end
end GinibrePoincare
