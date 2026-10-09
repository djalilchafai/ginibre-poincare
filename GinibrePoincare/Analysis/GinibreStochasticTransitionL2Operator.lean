module

public import GinibrePoincare.Analysis.GinibreStochasticTransitionL2Pullback
public import GinibrePoincare.Analysis.GinibreHamiltonianOriginalEquilibriumMarginals

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
local instance actualTransitionPathMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
local instance actualTransitionPathBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩

theorem ginibreOriginalEndpointInitialMeasurePreserving {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (α : ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P) (T : ℝ≥0) :
    MeasurePreserving (fun x : C(Icc (0 : ℝ) (T : ℝ), Configuration n) => x ⟨0, ⟨le_rfl, T.property⟩⟩)
      (ginibreOriginalEquilibriumPathLaw n α T P B) (ginibreMeasure n) :=
  ⟨(continuous_eval_const _).measurable, ginibreOriginalEquilibriumPathLaw_initial hn α P B hB T⟩

theorem ginibreOriginalEndpointTerminalMeasurePreserving {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) :
    MeasurePreserving (fun x : C(Icc (0 : ℝ) (T : ℝ), Configuration n) => x ⟨T, ⟨T.property, le_rfl⟩⟩)
      (ginibreOriginalEquilibriumPathLaw n α T P B) (ginibreMeasure n) :=
  ⟨(continuous_eval_const _).measurable, ginibreOriginalEquilibriumPathLaw_terminal hn α P B hB hiB T⟩

/-- Genuine original stochastic transition operator on the actual Ginibre L²
space, constructed from actual stationary Brownian endpoint pullbacks. -/
def ginibreOriginalStochasticL2Operator {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) :
    Lp ℝ 2 (ginibreMeasure n) →L[ℝ] Lp ℝ 2 (ginibreMeasure n) :=
  stationaryEndpointL2Operator (ginibreOriginalEquilibriumPathLaw n α T P B) (ginibreMeasure n)
    _ _ (ginibreOriginalEndpointInitialMeasurePreserving hn α P B hB T)
    (ginibreOriginalEndpointTerminalMeasurePreserving hn α P B hB hiB T)

theorem ginibreOriginalStochasticL2Operator_norm_le {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) (f : Lp ℝ 2 (ginibreMeasure n)) :
    ‖ginibreOriginalStochasticL2Operator hn α P B hB hiB T f‖≤‖f‖ :=
  stationaryEndpointL2Operator_norm_le _ _ _ _ _ _ f

theorem ginibreOriginalStochasticL2Operator_pairing {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) (f g : Lp ℝ 2 (ginibreMeasure n)) :
    inner ℝ f (ginibreOriginalStochasticL2Operator hn α P B hB hiB T g)=
      ∫ x, f (x ⟨0, ⟨le_rfl, T.property⟩⟩)*g (x ⟨T, ⟨T.property, le_rfl⟩⟩)
        ∂ginibreOriginalEquilibriumPathLaw n α T P B :=
  stationaryEndpointL2Operator_pairing _ _ _ _ _ _ f g

theorem ginibreOriginalStochasticL2Operator_symmetric {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) (f g : Lp ℝ 2 (ginibreMeasure n)) :
    inner ℝ f (ginibreOriginalStochasticL2Operator hn α P B hB hiB T g)=
      inner ℝ g (ginibreOriginalStochasticL2Operator hn α P B hB hiB T f) := by
  apply stationaryEndpointL2Operator_symmetric_pairing
  exact ⟨((continuous_eval_const _).measurable.prodMk (continuous_eval_const _).measurable).aemeasurable,
    ((continuous_eval_const _).measurable.prodMk (continuous_eval_const _).measurable).aemeasurable,
    ginibreOriginalEquilibriumPathLaw_joint_endpoint_swap hn α P B hB hiB T⟩

@[simp] theorem ginibreOriginalStochasticL2Operator_zero {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) :
    ginibreOriginalStochasticL2Operator hn α P B hB hiB 0=1 := by
  unfold ginibreOriginalStochasticL2Operator stationaryEndpointL2Operator
  exact (stationaryEndpointL2Pullback _ _ _
    (ginibreOriginalEndpointInitialMeasurePreserving hn α P B hB 0)).adjoint_comp_self

#print axioms ginibreOriginalStochasticL2Operator_zero
#print axioms ginibreOriginalStochasticL2Operator_norm_le
#print axioms ginibreOriginalStochasticL2Operator_pairing
#print axioms ginibreOriginalStochasticL2Operator_symmetric
end
end GinibrePoincare
