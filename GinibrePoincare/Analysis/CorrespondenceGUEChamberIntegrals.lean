module
public import GinibrePoincare.Analysis.CorrespondenceGUEChamberPartition
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
@[expose] public section
open MeasureTheory Set
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def guePermuteIsometry (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ.symm

theorem guePermuteIsometry_apply (n : ℕ) (σ : Equiv.Perm (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : guePermuteIsometry n σ x=guePermute n σ x := rfl

theorem guePermute_volume_preserving (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (guePermute n σ) volume volume :=
  (guePermuteIsometry n σ).measurePreserving

theorem gueChamber_weighted_integral {n : ℕ} (hn : 0<n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Continuous f)
    (hfs : ∀σ x,f (guePermute n σ x)=f x) (C : ℝ) (hb : ∀x,‖f x‖≤C) :
    (∫x,gueRawDensity n x*f x)=
      (Fintype.card (Equiv.Perm (Fin n)):ℝ)*(∫x,gueOrderedRawDensity n x*f x) := by
  have hi : Integrable (fun x => gueOrderedRawDensity n x*f x) volume := by
    apply ((gueOrderedRawDensity_integrable hn).mul_const C).mono'
      ((gueOrderedRawDensity_continuous n).mul hf).aestronglyMeasurable
    filter_upwards [] with x
    change ‖gueOrderedRawDensity n x*f x‖≤gueOrderedRawDensity n x*C
    rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (gueOrderedRawDensity_nonneg n x)]
    exact mul_le_mul_of_nonneg_left (hb x) (gueOrderedRawDensity_nonneg n x)
  have hper σ : Integrable (fun x => gueOrderedRawDensity n (guePermute n σ x)*f x) volume := by
    have h := (guePermute_volume_preserving n σ).integrable_comp_of_integrable hi
    change Integrable (fun x => gueOrderedRawDensity n (guePermute n σ x)*f (guePermute n σ x)) volume at h
    simpa only [hfs] using h
  have he (x) : gueRawDensity n x*f x=
      ∑σ : Equiv.Perm (Fin n),gueOrderedRawDensity n (guePermute n σ x)*f x := by
    rw [← Finset.sum_mul,gueChamber_density_partition]
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun σ _ => hper σ)]
  have hc σ : (∫x,gueOrderedRawDensity n (guePermute n σ x)*f x)=
      (∫x,gueOrderedRawDensity n x*f x) := by
    have h := (guePermute_volume_preserving n σ).integral_comp
      (guePermuteIsometry n σ).toHomeomorph.toMeasurableEquiv.measurableEmbedding
      (fun x => gueOrderedRawDensity n x*f x)
    simpa only [hfs] using h
  simp_rw [hc]
  simp

#print axioms gueChamber_weighted_integral
end
end GinibrePoincare
