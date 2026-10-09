module
public import GinibrePoincare.Analysis.CorrespondenceOperatorSemigroupComparison
public import GinibrePoincare.Analysis.CorrespondenceOperatorStochasticResolvent
public import GinibrePoincare.Analysis.GinibreStochasticTransitionL2Semigroup
public import GinibrePoincare.Analysis.GinibreStochasticTransitionL2ZeroSpeed
@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The original Brownian-driven Ginibre diffusion is exactly the unrestricted
analytic weak-form semigroup, at the paper's speed α/n. -/
theorem correspondenceOperator_stochastic_semigroup_eq {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (α : ℝ≥0) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) :
    ginibreOriginalStochasticL2Operator hn α P B hB hiB T =
      correspondenceOperatorRealEvolution n hn ((α/n)*T) := by
  by_cases hα : α=0
  · subst α
    apply ContinuousLinearMap.ext
    intro u
    rw [ginibreOriginalStochasticL2Operator_zero_speed]
    simp only [zero_div, zero_mul]
    exact (correspondenceOperatorRealEvolution_zero_apply hn u).symm
  · have hαp : 0<(α : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hα)
    have hc : 0<α/(n : ℝ≥0) := div_pos (pos_iff_ne_zero.mpr hα)
      (by exact_mod_cast hn)
    apply correspondenceOperatorContractionSemigroup_eq_from_actual_laplace hn
      (ginibreOriginalStochasticL2Operator hn α P B hB hiB)
      (ginibreOriginalStochasticL2Operator_strong_continuous hn α P B hB hiB)
      (ginibreOriginalStochasticL2Operator_norm_le hn α P B hB hiB)
      (by intro s t u; rw [ginibreOriginalStochasticL2Operator_semigroup]; rfl)
      (by intro u; rw [ginibreOriginalStochasticL2Operator_zero]; rfl) (α/n) hc
    intro u
    simpa only [NNReal.coe_div, NNReal.coe_natCast, ginibreOriginalStochasticL2Resolvent] using
      correspondenceOperator_stochastic_resolvent_eq hn α hαp P B hB hiB u

/-- The actual stochastic transition on complex observables acts componentwise
on the real and imaginary L² classes; these are the literal two components
of the complex expectation. -/
def correspondenceOperatorComplexStochasticTransition {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (α : ℝ≥0) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0)
    (f : GinibreFullComplexL2 n) : GinibreFullComplexL2 n :=
  ginibreFullComplexOfReal n
    (ginibreOriginalStochasticL2Operator hn α P B hB hiB T (ginibreFullComplexRe n f)) +
  Complex.I • ginibreFullComplexOfReal n
    (ginibreOriginalStochasticL2Operator hn α P B hB hiB T (ginibreFullComplexIm n f))

/-- Stochastic and analytic identification on the entire unrestricted complex
L² space, including all nonsymmetric observables. -/
theorem correspondenceOperator_complex_stochastic_semigroup_eq {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (α : ℝ≥0) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0)
    (f : GinibreFullComplexL2 n) :
    correspondenceOperatorComplexStochasticTransition hn α P B hB hiB T f =
      correspondenceOperatorEvolution n hn ((α/n)*T) f := by
  unfold correspondenceOperatorComplexStochasticTransition
  rw [correspondenceOperator_stochastic_semigroup_eq hn α P B hB hiB T]
  rw [← correspondenceOperatorEvolution_ofReal,← correspondenceOperatorEvolution_ofReal,
    ← map_smul,← map_add, ginibreFullComplex_decomposition]

#print axioms correspondenceOperator_complex_stochastic_semigroup_eq
#print axioms correspondenceOperator_stochastic_semigroup_eq
end
end GinibrePoincare
