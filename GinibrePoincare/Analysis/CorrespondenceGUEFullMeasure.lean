module
public import GinibrePoincare.Analysis.CorrespondenceGUEChamberIntegrals
@[expose] public section
open MeasureTheory Filter Set
open scoped ENNReal BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem gueRawDensity_integrable {n : ℕ} (hn : 0<n) : Integrable (gueRawDensity n) volume := by
  have hσ (σ : Equiv.Perm (Fin n)) : Integrable (fun x => gueOrderedRawDensity n (guePermute n σ x)) volume :=
    (guePermute_volume_preserving n σ).integrable_comp_of_integrable (gueOrderedRawDensity_integrable hn)
  simpa only [gueChamber_density_partition] using integrable_finsetSum Finset.univ (fun σ _ => hσ σ)

theorem gueRawDensity_partition_pos {n : ℕ} (hn : 0<n) : 0<∫x,gueRawDensity n x := by
  have h := gueChamber_weighted_integral hn (fun _ => 1) continuous_const
    (by intros; rfl) 1 (by intros; norm_num)
  simp only [mul_one] at h
  rw [h]
  exact mul_pos (by exact_mod_cast Fintype.card_pos) (gueOrderedRawDensity_partition_pos hn)

def gueFullMeasure (n : ℕ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  (ENNReal.ofReal (∫x,gueRawDensity n x))⁻¹ • volume.withDensity (fun x => ENNReal.ofReal (gueRawDensity n x))

theorem gueRawDensity_nonneg (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : 0≤gueRawDensity n x := by
  unfold gueRawDensity
  positivity

theorem gueRawDensity_continuous (n : ℕ) : Continuous (gueRawDensity n) := by
  unfold gueRawDensity
  fun_prop

theorem gueFullMeasure_probability {n : ℕ} (hn : 0<n) : IsProbabilityMeasure (gueFullMeasure n) := by
  constructor
  unfold gueFullMeasure
  rw [Measure.smul_apply,withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal (gueRawDensity_integrable hn)
      (Eventually.of_forall (gueRawDensity_nonneg n))]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr (gueRawDensity_partition_pos hn)) ENNReal.ofReal_ne_top

theorem gueFullMeasure_integral (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫x,f x ∂gueFullMeasure n)=(∫x,gueRawDensity n x*f x)/(∫x,gueRawDensity n x) := by
  unfold gueFullMeasure
  rw [integral_smul_measure,integral_withDensity_eq_integral_toReal_smul (μ := volume)
    (f := fun x => ENNReal.ofReal (gueRawDensity n x))
    ((gueRawDensity_continuous n).measurable.ennreal_ofReal)
    (Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)) f]
  simp only [ENNReal.toReal_inv,ENNReal.toReal_ofReal (gueRawDensity_nonneg n _),smul_eq_mul]
  rw [ENNReal.toReal_ofReal (integral_nonneg (gueRawDensity_nonneg n))]
  ring

theorem gueFullMeasure_symmetric_integral {n : ℕ} (hn : 0<n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Continuous f)
    (hs : ∀σ x,f (guePermute n σ x)=f x) (C : ℝ) (hb : ∀x,‖f x‖≤C) :
    (∫x,f x ∂gueFullMeasure n)=(∫x,f x ∂gueOrderedMeasure n) := by
  rw [gueFullMeasure_integral,gueOrderedMeasure_integral,
    gueChamber_weighted_integral hn f hf hs C hb]
  have hp := gueChamber_weighted_integral hn (fun _ => 1) continuous_const
    (by intros; rfl) 1 (by intros; norm_num)
  simp only [mul_one] at hp
  rw [hp]
  have hc : (Fintype.card (Equiv.Perm (Fin n)):ℝ)≠0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp [hc]

#print axioms gueFullMeasure_symmetric_integral
#print axioms gueFullMeasure_probability
end
end GinibrePoincare
