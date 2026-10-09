module

public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityCoordinates
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Restrict

@[expose] public section
open MeasureTheory Measure
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000

theorem ginibreLocalRegularity_coordinate_restricted_memLp
    (n : ℕ) (K : Set (Configuration n)) (u : Configuration n → ℂ)
    (hu : MemLp u 2 ((volume : Measure (Configuration n)).restrict K)) :
    MemLp (fun x => u ((configurationEuclideanEquiv n).symm x)) 2
      ((volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))).restrict
        ((configurationEuclideanEquiv n) '' K)) := by
  let e := (configurationEuclideanEquiv n).toHomeomorph.toMeasurableEquiv
  let q := fun x => u (e.symm x)
  have hm : MemLp q 2 (((volume : Measure (Configuration n)).restrict K).map e) := by
    apply e.memLp_map_measure_iff.mpr
    simpa only [q, Function.comp_def, MeasurableEquiv.symm_apply_apply] using hu
  obtain ⟨c, hc, he⟩ := ginibreLocalRegularity_coordinate_volume n
  have hmap : (((volume : Measure (Configuration n)).restrict K).map e) =
      (c : ℝ≥0∞) • ((volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))).restrict (e '' K)) := by
    have hr := e.restrict_map (volume : Measure (Configuration n)) (e '' K)
    rw [Set.preimage_image_eq _ e.injective] at hr
    change ((volume : Measure (Configuration n)).map (configurationEuclideanEquiv n)).restrict (e '' K) = _ at hr
    rw [he, Measure.restrict_smul] at hr
    exact hr.symm
  rw [hmap] at hm
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc.ne'
  have hmi := hm.smul_measure (c := (c : ℝ≥0∞)⁻¹) (ENNReal.inv_ne_top.mpr hc0)
  rw [smul_smul, ENNReal.inv_mul_cancel hc0 ENNReal.coe_ne_top, one_smul] at hmi
  exact hmi

theorem ginibreLocalRegularity_coordinate_pullback_memLp
    {V : Type*} [NormedAddCommGroup V] (n : ℕ)
    (g : EuclideanSpace ℝ (Fin n × Fin 2) → V)
    (hg : MemLp g 2 (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))) :
    MemLp (g ∘ configurationEuclideanEquiv n) 2 (volume : Measure (Configuration n)) := by
  obtain ⟨c, hc, he⟩ := ginibreLocalRegularity_coordinate_volume n
  have hi := hg.smul_measure (c := (c : ℝ≥0∞)) ENNReal.coe_ne_top
  change MemLp g 2 (c • (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2)))) at hi
  rw [← he] at hi
  exact hi.comp_of_map (configurationEuclideanEquiv n).continuous.measurable.aemeasurable

#print axioms ginibreLocalRegularity_coordinate_pullback_memLp
#print axioms ginibreLocalRegularity_coordinate_restricted_memLp
end
end GinibrePoincare
