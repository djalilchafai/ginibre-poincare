module

public import GinibrePoincare.Analysis.GinibreStochasticTransitionBoundedOperator
public import GinibrePoincare.Analysis.GinibreStochasticCenterZeroSpeed

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem ginibreStationaryContinuousTransitionMean_zero_speed {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (z : Configuration n) (hz : CollisionFree z)
    (v : Configuration n → ℝ) (T : ℝ≥0) :
    ginibreStationaryContinuousTransitionMean 0 B P v (T:ℝ) z=v z := by
  have hm := ginibreStationaryContinuousTransitionMean_eq_original hn 0 P B hB hiB v z hz (T:ℝ)
  simp only [NNReal.coe_zero,Real.toNNReal_coe] at hm
  rw [hm]
  have he := ginibreBrownianMaximalProcess_zero_speed_constant hn z hz B P hB hiB
  rw [integral_congr_ae (he.mono fun ω hω => congrArg v (hω T))]
  simp

theorem ginibreOriginalStochasticL2Operator_zero_speed {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) :
    ginibreOriginalStochasticL2Operator hn 0 P B hB hiB T=1 := by
  letI := ginibreMeasure_isProbabilityMeasure hn
  have he : (ginibreOriginalStochasticL2Operator hn 0 P B hB hiB T :
      Lp ℝ 2 (ginibreMeasure n) → Lp ℝ 2 (ginibreMeasure n))=id := by
    apply (BoundedContinuousFunction.toLp_denseRange ℝ (ginibreMeasure n) ℝ (by norm_num : (2:ℝ≥0∞)≠∞)).equalizer
      (ginibreOriginalStochasticL2Operator hn 0 P B hB hiB T).continuous continuous_id
    funext v
    let g := BoundedContinuousFunction.toLp 2 (ginibreMeasure n) ℝ v
    have hg := BoundedContinuousFunction.coeFn_toLp (p := 2) (μ := ginibreMeasure n) (𝕜 := ℝ) v
    have hb := ginibreOriginalStochasticL2Operator_bounded_representative hn 0 P B hB hiB T g v hg
      v.continuous.measurable ‖v‖ (fun z => v.norm_coe_le_norm z)
    change ginibreOriginalStochasticL2Operator hn 0 P B hB hiB T g=g
    apply Lp.ext
    filter_upwards [ginibre_ae_collisionFree n hn,hb.2.2,hg] with z hz hleft hright
    rw [hleft,hright]
    exact ginibreStationaryContinuousTransitionMean_zero_speed hn P B hB hiB z hz v T
  apply ContinuousLinearMap.ext
  intro g
  exact congr_fun he g

#print axioms ginibreOriginalStochasticL2Operator_zero_speed
end
end GinibrePoincare
