module

public import GinibrePoincare.Analysis.GinibreStochasticTransitionBoundedResolvent

@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
theorem actualL2_eq_toLp_of_pairings {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (u : Lp ℝ 2 μ) (r : E → ℝ) (hr : MemLp r 2 μ)
    (hp : ∀ g : Lp ℝ 2 μ, inner ℝ g u=∫ z, g z*r z ∂μ) : u=hr.toLp r := by
  apply ext_inner_left ℝ
  intro g
  rw [hp,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hr.coeFn_toLp] with z hz
  simp [hz,mul_comm]

theorem ginibreOriginalStochasticL2Operator_bounded_representative {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0)
    (f : Lp ℝ 2 (ginibreMeasure n)) (v : Configuration n → ℝ)
    (hf : (f : Configuration n → ℝ)=ᵐ[ginibreMeasure n] v)
    (hv : Measurable v) (C : ℝ) (hC : ∀ z, ‖v z‖≤C) :
    let r := fun z => ginibreStationaryContinuousTransitionMean α B P v (T:ℝ) z
    Measurable r ∧ (∀ z, ‖r z‖≤C) ∧
      ((ginibreOriginalStochasticL2Operator hn α P B hB hiB T f : Lp ℝ 2 (ginibreMeasure n)) : Configuration n → ℝ)=ᵐ[ginibreMeasure n] r := by
  letI := ginibreMeasure_isProbabilityMeasure hn
  let r := fun z => ginibreStationaryContinuousTransitionMean α B P v (T:ℝ) z
  have hbase := ginibreStationaryContinuousTransitionMean_joint_measurable hn α P B hB v hv
  have hparam : Measurable (fun z : Configuration n => ((T:ℝ),z)) := measurable_const.prodMk measurable_id
  have hm : Measurable r := hbase.comp hparam
  have hb (z : Configuration n) : ‖r z‖≤C := ginibreStationaryContinuousTransitionMean_bound α P B v C hC (T:ℝ) z
  have hr : MemLp r 2 (ginibreMeasure n) := MemLp.of_bound hm.aestronglyMeasurable C (ae_of_all _ hb)
  have he : ginibreOriginalStochasticL2Operator hn α P B hB hiB T f=hr.toLp r :=
    actualL2_eq_toLp_of_pairings (ginibreMeasure n) _ r hr (fun g =>
      ginibreOriginalStochasticL2Operator_measurable_mean_pairing hn α P B hB hiB T g f v hf hv C hC)
  refine ⟨hm,hb,?_⟩
  rw [he]
  exact hr.coeFn_toLp


#print axioms ginibreOriginalStochasticL2Operator_bounded_representative
end
end GinibrePoincare
