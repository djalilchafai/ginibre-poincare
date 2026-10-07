module

public import GinibrePoincare.Analysis.BrownianPredictableMeasureTransform
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def scaledStandardGaussian (v : ℝ≥0) : Measure E :=
  (stdGaussian E).map (fun x => Real.sqrt (v : ℝ) • x)

instance scaledStandardGaussian_isProbability (v : ℝ≥0) :
    IsProbabilityMeasure (scaledStandardGaussian E v) := by
  unfold scaledStandardGaussian
  infer_instance

theorem scaledStandardGaussian_measurePreserving (v : ℝ≥0) (U : E ≃ₗᵢ[ℝ] E) :
    MeasurePreserving U (scaledStandardGaussian E v) (scaledStandardGaussian E v) := by
  refine ⟨U.continuous.measurable, ?_⟩
  unfold scaledStandardGaussian
  rw [Measure.map_map U.continuous.measurable (by fun_prop)]
  have he : (fun x => U (Real.sqrt (v : ℝ) • x)) =
      (fun x => Real.sqrt (v : ℝ) • U x) := by funext x; exact U.map_smul _ _
  change (stdGaussian E).map (fun x => U (Real.sqrt (v : ℝ) • x)) = _
  rw [he]
  change (stdGaussian E).map ((fun x => Real.sqrt (v : ℝ) • x) ∘ U) = _
  rw [← Measure.map_map (by fun_prop) U.continuous.measurable, stdGaussian_map U]

theorem independent_past_orthogonal_gaussian_transform {Ω A : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A]
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure A) [IsProbabilityMeasure ν]
    (v : ℝ≥0) (Y : Ω → A) (X : Ω → E) (hY : HasLaw Y ν P)
    (hX : HasLaw X (scaledStandardGaussian E v) P) (hi : IndepFun Y X P)
    (U : A → E ≃ₗᵢ[ℝ] E) (hU : Measurable (fun p : A × E => U p.1 p.2)) :
    HasLaw (fun ω => U (Y ω) (X ω)) (scaledStandardGaussian E v) P ∧
      IndepFun Y (fun ω => U (Y ω) (X ω)) P := by
  exact independent_past_measure_transform P ν (scaledStandardGaussian E v) Y X hY hX hi
    (fun a x => U a x) hU (fun a => scaledStandardGaussian_measurePreserving E v (U a))

end
end GinibrePoincare
