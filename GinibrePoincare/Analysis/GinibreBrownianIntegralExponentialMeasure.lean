module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralExponentialNatural
public import GinibrePoincare.Analysis.BrownianIntegralGirsanovMeasure

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- The actual stochastic exponential is strictly positive for every input. -/
theorem brownianVectorExponentialIntegralDensity_pos {Ω ι : Type*} [Fintype ι]
    (F : ι → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (I : ι → Ω → ℝ) (ω : Ω) :
    0 < brownianVectorExponentialIntegralDensity F T I ω := Real.exp_pos _

/-- Its genuine normalized measure is equivalent to the original measure and
 inherits completeness; positivity is derived from the literal exponential. -/
theorem brownianVectorExponentialIntegralDensity_measure_properties {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω) [P.IsComplete]
    (F : ι → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (I : ι → Ω → ℝ)
    (hi : Integrable (brownianVectorExponentialIntegralDensity F T I) P)
    (h1 : (∫ ω, brownianVectorExponentialIntegralDensity F T I ω ∂P)=1) :
    let Q := P.withDensity (fun ω => ENNReal.ofReal (brownianVectorExponentialIntegralDensity F T I ω))
    IsProbabilityMeasure Q ∧ Q ≪ P ∧ P ≪ Q ∧ Q.IsComplete := by
  dsimp only
  have hpos : ∀ᵐ ω ∂P, ENNReal.ofReal (brownianVectorExponentialIntegralDensity F T I ω) ≠ 0 :=
    Eventually.of_forall fun ω => (ENNReal.ofReal_pos.mpr
      (brownianVectorExponentialIntegralDensity_pos F T I ω)).ne'
  have hPQ := withDensity_absolutelyContinuous'
    (ENNReal.measurable_ofReal.comp_aemeasurable hi.aestronglyMeasurable.aemeasurable) hpos
  refine ⟨gaussianDensity_isProbabilityMeasure_of_integral_one P _ hi
    (Eventually.of_forall fun ω => (brownianVectorExponentialIntegralDensity_pos F T I ω).le) h1,
    withDensity_absolutelyContinuous _ _, hPQ,?_⟩
  apply Measure.isComplete_iff.mpr
  intro s hs
  exact measurableSet_of_null (hPQ hs)

end
end GinibrePoincare
