module

public import GinibrePoincare.Analysis.BrownianOrthogonalIndependentProduct
public import GinibrePoincare.Analysis.EquilibriumProbability

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
local instance : MeasurableSpace C(ℝ, ℂ) := borel _
local instance : BorelSpace C(ℝ, ℂ) := ⟨rfl⟩

/-- The actual Ginibre initial center and its Brownian noise are independent of
 the actual initial relative configuration and its entire relative noise path. -/
theorem ginibre_equilibrium_center_relative_inputs_independent {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ) :
    IndepFun
      (fun p => (coordinateSum p.1,
        ginibreContinuousNoiseCenter n (ginibreBrownianFullContinuousNoise n B α p.2)))
      (fun p => (recenteredConfiguration n p.1,
        ginibreContinuousNoiseRecenter n (ginibreBrownianFullContinuousNoise n B α p.2)))
      ((ginibreMeasure n).prod P) := by
  letI := ginibreMeasure_isProbabilityMeasure hn
  have hN := ginibreBrownianFullContinuousNoise_measurable n B P hB α
  apply independent_pairs_on_product_measure (ginibreMeasure n) P
    (coordinateSum : Configuration n → ℂ) (recenteredConfiguration n)
    (fun ω => ginibreContinuousNoiseCenter n (ginibreBrownianFullContinuousNoise n B α ω))
    (fun ω => ginibreContinuousNoiseRecenter n (ginibreBrownianFullContinuousNoise n B α ω))
  · convert (coordinateSumCLM n).continuous.measurable using 1
    funext z
    exact (coordinateSumCLM_apply n z).symm
  · convert (recenteredCLM n).continuous.measurable using 1
    funext z
    exact (recenteredCLM_apply n z).symm
  · exact (ginibreContinuousNoiseCenter_continuous n).measurable.comp hN
  · exact (ginibreContinuousNoiseRecenter_continuous n).measurable.comp hN
  · exact coordinateSum_recentered_indepFun n hn
  · exact brownianFamily_actual_continuous_center_recenter_noise_independent hn B P hB hind α

end
end GinibrePoincare
