module

public import GinibrePoincare.Analysis.GaussianFourierCoordinates
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section
open MeasureTheory Measure
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreLocalRegularity_coordinate_volume (n : ℕ) :
    ∃ c : ℝ≥0, 0 < c ∧
      (volume : Measure (Configuration n)).map (configurationEuclideanEquiv n) =
        c • (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))) := by
  let e := configurationEuclideanEquiv n
  let μ := (volume : Measure (Configuration n)).map e
  letI : IsAddHaarMeasure μ := e.isAddHaarMeasure_map volume
  refine ⟨addHaarScalarFactor μ volume,addHaarScalarFactor_pos_of_isAddHaarMeasure μ volume,?_⟩
  exact isAddLeftInvariant_eq_smul μ volume

theorem ginibreLocalRegularity_coordinate_integral (n : ℕ) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ f : EuclideanSpace ℝ (Fin n × Fin 2) → ℂ,
      (∫ z : Configuration n, f (configurationEuclideanEquiv n z)) =
        (c : ℝ) • (∫ x, f x) := by
  obtain ⟨c,hc,he⟩ := ginibreLocalRegularity_coordinate_volume n
  refine ⟨c,hc,?_⟩
  intro f
  have hm := integral_map_equiv (μ := (volume : Measure (Configuration n)))
    (configurationEuclideanEquiv n).toHomeomorph.toMeasurableEquiv f
  change (∫ x, f x ∂(volume : Measure (Configuration n)).map (configurationEuclideanEquiv n)) =
    (∫ z : Configuration n, f (configurationEuclideanEquiv n z)) at hm
  rw [he,integral_smul_nnreal_measure] at hm
  exact hm.symm

#print axioms ginibreLocalRegularity_coordinate_integral
#print axioms ginibreLocalRegularity_coordinate_volume
end
end GinibrePoincare
