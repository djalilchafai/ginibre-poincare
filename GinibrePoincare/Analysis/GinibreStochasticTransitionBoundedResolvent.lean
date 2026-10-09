module

public import GinibrePoincare.Analysis.GinibreStochasticTransitionCoreResolvent
public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLaplaceBounds

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1000000

/-- The genuine pointwise normalized Laplace representative of the stochastic
L² resolvent, with the same global bound as its bounded measurable input. -/
theorem ginibreOriginalStochasticL2Resolvent_bounded_representative {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) {c : ℝ} (hc : 0<c)
    (f : Lp ℝ 2 (ginibreMeasure n)) (v : Configuration n → ℝ)
    (hf : (f : Configuration n → ℝ)=ᵐ[ginibreMeasure n] v)
    (hv : Measurable v) (C : ℝ) (hC : ∀ z, ‖v z‖≤C) :
    let r := fun z => ∫ t in Ioi (0 : ℝ), c*Real.exp (-c*t)*
      ginibreStationaryContinuousTransitionMean α B P v t z
    Measurable r ∧ (∀ z, ‖r z‖≤C) ∧
      (ginibreOriginalStochasticL2Resolvent hn α P B hB hiB c f : Configuration n → ℝ)=ᵐ[ginibreMeasure n] r := by
  letI := ginibreMeasure_isProbabilityMeasure hn
  let r := fun z => ∫ t in Ioi (0 : ℝ), c*Real.exp (-c*t)*
    ginibreStationaryContinuousTransitionMean α B P v t z
  have hm := ginibreStationaryContinuousTransitionMean_joint_measurable hn α P B hB v hv
  have hm' := hm.comp (measurable_swap : Measurable (@Prod.swap (Configuration n) ℝ))
  have he : Measurable (fun q : Configuration n × ℝ => c*Real.exp (-c*q.2)) :=
    (measurable_const (a := c)).mul (Real.measurable_exp.comp
      ((measurable_const (a := -c)).mul measurable_snd))
  have hw := he.mul hm'
  have hri : Measurable r := (hw.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))).measurable
  have hrb (z : Configuration n) : ‖r z‖≤C := by
    have hs : AEStronglyMeasurable (fun t : ℝ => ginibreStationaryContinuousTransitionMean α B P v t z)
        (volume.restrict (Ioi 0)) :=
      (hm.comp (measurable_id.prodMk (measurable_const (a := z)))).aestronglyMeasurable
    simpa [r, smul_eq_mul] using (actualNormalizedLaplaceIntegral_norm_bound
      (fun t : ℝ => ginibreStationaryContinuousTransitionMean α B P v t z) c C hc hs
      (ae_of_all _ fun t => ginibreStationaryContinuousTransitionMean_bound α P B v C hC t z)).2
  have hr : MemLp r 2 (ginibreMeasure n) := MemLp.of_bound hri.aestronglyMeasurable C (ae_of_all _ hrb)
  have he : ginibreOriginalStochasticL2Resolvent hn α P B hB hiB c f=hr.toLp r :=
    ginibreOriginalStochasticL2Resolvent_of_bounded_point_identity hn α P B hB hiB hc
      f (hr.toLp r) v hf hv C hC hr.coeFn_toLp.symm
  exact ⟨hri, hrb, he ▸ hr.coeFn_toLp⟩

#print axioms ginibreOriginalStochasticL2Resolvent_bounded_representative
end
end GinibrePoincare
