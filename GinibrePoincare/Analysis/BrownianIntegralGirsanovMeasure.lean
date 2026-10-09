module

public import GinibrePoincare.Analysis.BrownianIntegralGirsanovVectorDensityLimit

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section

theorem gaussianDensity_isProbabilityMeasure_of_lintegral_one
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : Ω → ℝ)
    (hD : (∫⁻ ω, ENNReal.ofReal (D ω) ∂P)=1) :
    IsProbabilityMeasure (P.withDensity (fun ω => ENNReal.ofReal (D ω))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact hD

theorem gaussianDensity_isProbabilityMeasure_of_integral_one
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (D : Ω → ℝ)
    (hDi : Integrable D P) (hDp : 0≤ᵐ[P] D) (hD : (∫ ω, D ω ∂P)=1) :
    IsProbabilityMeasure (P.withDensity (fun ω => ENNReal.ofReal (D ω))) := by
  apply gaussianDensity_isProbabilityMeasure_of_lintegral_one
  rw [← ofReal_integral_eq_lintegral_ofReal hDi hDp, hD, ENNReal.ofReal_one]

/-- The original predictable vector RN density defines an actual probability
measure at every finite chronological grid. -/
theorem brownianPredictableVectorGaussianDensity_isProbabilityMeasure
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (h : ℕ → Ω → ι → ℝ) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hh : ∀ k, @Measurable Ω (ι→ℝ) (ginibreBrownianAugmentedFiltration B P hB (τ k)) _ (h k))
    (N : ℕ) : IsProbabilityMeasure (P.withDensity
      (fun ω => ENNReal.ofReal (brownianPredictableVectorGaussianDensity B h τ N ω))) :=
  gaussianDensity_isProbabilityMeasure_of_lintegral_one P _
    (brownianPredictableVectorGaussianDensity_lintegral B P hB hind h τ hτ hh N)

end
end GinibrePoincare
