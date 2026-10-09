module

public import GinibrePoincare.Analysis.GinibreStochasticTransitionBoundedResolvent
public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLaplaceOperator
public import GinibrePoincare.Analysis.GinibreTransitionAnalyticBoundedDense

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The actual stochastic normalized Laplace integral bundled as a continuous linear map. -/
def ginibreOriginalStochasticL2ResolventOperator {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (c : ℝ) (hc : 0<c) :
    Lp ℝ 2 (ginibreMeasure n) →L[ℝ] Lp ℝ 2 (ginibreMeasure n) :=
  actualContractionLaplaceOperator
    (ginibreOriginalStochasticL2Operator hn α P B hB hiB)
    (ginibreOriginalStochasticL2Operator_strong_continuous hn α P B hB hiB)
    (ginibreOriginalStochasticL2Operator_norm_le hn α P B hB hiB) c hc

theorem ginibreOriginalStochasticL2ResolventOperator_apply {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (c : ℝ) (hc : 0<c)
    (u : Lp ℝ 2 (ginibreMeasure n)) :
    ginibreOriginalStochasticL2ResolventOperator hn α P B hB hiB c hc u =
      ginibreOriginalStochasticL2Resolvent hn α P B hB hiB c u := rfl

/-- A globally bounded measurable version of every essentially bounded real L² value. -/
theorem ginibreBoundedLp_measurable_version {n : ℕ} (hn : 0<n)
    (f : Lp ℝ 2 (ginibreMeasure n)) (A : ℝ)
    (hb : ∀ᵐ z ∂ginibreMeasure n, ‖f z‖≤A) :
    ∃ v : Configuration n → ℝ, Measurable v ∧ (∀ z, ‖v z‖≤max A 0) ∧
      (f : Configuration n → ℝ)=ᵐ[ginibreMeasure n] v := by
  let v := actualBoundedRealVersion f (max A 0)
  have hm : Measurable v := by
    exact Measurable.ite
      (measurableSet_le (Lp.stronglyMeasurable f).measurable.norm measurable_const)
      (Lp.stronglyMeasurable f).measurable measurable_const
  have hb' : ∀ᵐ z ∂ginibreMeasure n, ‖f z‖≤max A 0 := hb.mono fun z hz => hz.trans (le_max_left _ _)
  exact ⟨v, hm, actualBoundedRealVersion_bound f (max A 0) (le_max_right _ _),
    (actualBoundedRealVersion_ae _ f _ hb').symm⟩

/-- Equality on genuinely bounded values extends to the full symmetric L² source,
with no assumption that either target operator preserves symmetry. -/
theorem ginibreSymmetricSource_operators_eq_of_bounded_values (n : ℕ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R S : ginibreFullSymmetricValues n →L[ℝ] E)
    (heq : ∀ u : ginibreFullSymmetricValues n,
      (∃ A : ℝ, ∀ᵐ z ∂ginibreMeasure n, ‖u.val z‖≤A) → R u=S u) : R=S := by
  apply ContinuousLinearMap.ext
  intro u
  have ht := ginibreFullSymmetricBoundedTruncation_tendsto n u
  have hh (m : ℕ) : R (ginibreFullSymmetricBoundedTruncation n m u)=
      S (ginibreFullSymmetricBoundedTruncation n m u) :=
    heq _ ⟨2*((m : ℝ)+1), ginibreFullSymmetricBoundedTruncation_bound n m u⟩
  have hRt := R.continuous.tendsto u |>.comp ht
  have hSt : Tendsto (fun m => R (ginibreFullSymmetricBoundedTruncation n m u)) atTop (𝓝 (S u)) := by
    convert (S.continuous.tendsto u |>.comp ht) using 1
    funext m
    exact hh m
  exact tendsto_nhds_unique hRt hSt

#print axioms ginibreOriginalStochasticL2ResolventOperator
#print axioms ginibreBoundedLp_measurable_version
#print axioms ginibreSymmetricSource_operators_eq_of_bounded_values
end
end GinibrePoincare
