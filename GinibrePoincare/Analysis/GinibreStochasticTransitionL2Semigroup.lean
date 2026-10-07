module

public import GinibrePoincare.Analysis.GinibreStochasticTransitionBoundedOperator
public import GinibrePoincare.Analysis.GinibreStochasticTransitionMarkovMean

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- Genuine Chapman–Kolmogorov identity for the actual stochastic L²
operators. The Brownian restart and future independence are derived internally. -/
theorem ginibreOriginalStochasticL2Operator_semigroup {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (s t : ℝ≥0) :
    ginibreOriginalStochasticL2Operator hn α P B hB hiB (s+t)=
      (ginibreOriginalStochasticL2Operator hn α P B hB hiB s).comp
        (ginibreOriginalStochasticL2Operator hn α P B hB hiB t) := by
  letI := ginibreMeasure_isProbabilityMeasure hn
  let A := ginibreOriginalStochasticL2Operator hn α P B hB hiB
  have he : (fun u => A (s+t) u)=(fun u => A s (A t u)) := by
    apply (BoundedContinuousFunction.toLp_denseRange ℝ (ginibreMeasure n) ℝ (by norm_num : (2:ℝ≥0∞)≠∞)).equalizer
      (A (s+t)).continuous ((A s).continuous.comp (A t).continuous)
    funext v
    let g := BoundedContinuousFunction.toLp 2 (ginibreMeasure n) ℝ v
    have hg := BoundedContinuousFunction.coeFn_toLp (p := 2) (μ := ginibreMeasure n) (𝕜 := ℝ) v
    have hC (z : Configuration n) : ‖v z‖≤‖v‖ := v.norm_coe_le_norm z
    have ht := ginibreOriginalStochasticL2Operator_bounded_representative hn α P B hB hiB t g v hg v.continuous.measurable ‖v‖ hC
    have hs := ginibreOriginalStochasticL2Operator_bounded_representative hn α P B hB hiB s (A t g)
      (fun z => ginibreStationaryContinuousTransitionMean α B P v (t:ℝ) z)
      ht.2.2 ht.1 ‖v‖ ht.2.1
    have hst := ginibreOriginalStochasticL2Operator_bounded_representative hn α P B hB hiB (s+t) g v hg v.continuous.measurable ‖v‖ hC
    change A (s+t) g=A s (A t g)
    apply Lp.ext
    filter_upwards [ginibre_ae_collisionFree n hn,hst.2.2,hs.2.2] with z hz hleft hright
    change (ginibreOriginalStochasticL2Operator hn α P B hB hiB (s+t) g) z=
      (ginibreOriginalStochasticL2Operator hn α P B hB hiB s (A t g)) z
    rw [hleft,hright]
    exact ginibreStationaryContinuousTransitionMean_semigroup hn α P B hB hiB z hz s t v v.continuous.measurable ‖v‖ hC
  apply ContinuousLinearMap.ext
  intro u
  exact congr_fun he u

#print axioms ginibreOriginalStochasticL2Operator_semigroup
end
end GinibrePoincare
