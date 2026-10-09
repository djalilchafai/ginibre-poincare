module

public import GinibrePoincare.Analysis.GinibreStochasticTransitionPermutationOperator
public import GinibrePoincare.Analysis.GinibreStochasticTransitionL2Sampling
public import GinibrePoincare.Analysis.GinibreStochasticTransitionResolventIdentification
public import GinibrePoincare.Analysis.GinibreTransitionAnalyticResolventSemigroupComparison

@[expose] public section

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def ginibreOriginalSymmetricStochasticL2Operator {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) :
    ginibreFullSymmetricValues n →L[ℝ] ginibreFullSymmetricValues n :=
  ((ginibreOriginalStochasticL2Operator hn α P B hB hiB T).comp
    (ginibreFullSymmetricValues n).subtypeL).codRestrict (ginibreFullSymmetricValues n)
      (ginibreOriginalStochasticL2Operator_preserves_symmetric hn α P B hB hiB T)

theorem ginibreOriginalSymmetricStochasticL2Operator_val {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) (u : ginibreFullSymmetricValues n) :
    (ginibreOriginalSymmetricStochasticL2Operator hn α P B hB hiB T u).val=
      ginibreOriginalStochasticL2Operator hn α P B hB hiB T u.val := rfl

theorem ginibreOriginalSymmetricStochasticL2Operator_continuous {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (u : ginibreFullSymmetricValues n) :
    Continuous (fun T => ginibreOriginalSymmetricStochasticL2Operator hn α P B hB hiB T u) :=
  Continuous.subtype_mk (ginibreOriginalStochasticL2Operator_strong_continuous hn α P B hB hiB u.val) _

theorem ginibreOriginalSymmetricStochasticL2Operator_norm_le {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) (u : ginibreFullSymmetricValues n) :
    ‖ginibreOriginalSymmetricStochasticL2Operator hn α P B hB hiB T u‖≤‖u‖ :=
  ginibreOriginalStochasticL2Operator_norm_le hn α P B hB hiB T u.val

theorem ginibreOriginalSymmetricStochasticL2Operator_zero {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (u : ginibreFullSymmetricValues n) :
    ginibreOriginalSymmetricStochasticL2Operator hn α P B hB hiB 0 u=u := by
  apply Subtype.ext
  rw [ginibreOriginalSymmetricStochasticL2Operator_val, ginibreOriginalStochasticL2Operator_zero]
  rfl

theorem ginibreOriginalSymmetricStochasticL2Operator_laplace {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (α : ℝ≥0) (hα : 0<(α : ℝ)) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (u : ginibreFullSymmetricValues n) :
    (∫ s in Ioi (0 : ℝ), (((α : ℝ)/(n : ℝ))*Real.exp (-((α : ℝ)/(n : ℝ))*s)) •
      ginibreOriginalSymmetricStochasticL2Operator hn α P B hB hiB s.toNNReal u)=
      ginibreFullSymmetricResolvent n hn u := by
  have hc : 0<(α : ℝ)/(n : ℝ) := div_pos hα (Nat.cast_pos.mpr hn)
  have hI := actualContractionLaplace_integrable
    (ginibreOriginalSymmetricStochasticL2Operator hn α P B hB hiB)
    (ginibreOriginalSymmetricStochasticL2Operator_continuous hn α P B hB hiB)
    (ginibreOriginalSymmetricStochasticL2Operator_norm_le hn α P B hB hiB)
    ((α : ℝ)/(n : ℝ)) hc u
  apply Subtype.ext
  change (ginibreFullSymmetricValues n).subtypeL
    (∫ s in Ioi (0 : ℝ), (((α : ℝ)/(n : ℝ))*Real.exp (-((α : ℝ)/(n : ℝ))*s)) •
      ginibreOriginalSymmetricStochasticL2Operator hn α P B hB hiB s.toNNReal u)=_
  rw [← (ginibreFullSymmetricValues n).subtypeL.integral_comp_comm hI]
  change ginibreOriginalStochasticL2Resolvent hn α P B hB hiB ((α : ℝ)/(n : ℝ)) u.val=_
  exact ginibreOriginalStochasticL2Resolvent_eq_analytic hn α hα P B hB hiB u

#print axioms ginibreOriginalSymmetricStochasticL2Operator_laplace
end
end GinibrePoincare
