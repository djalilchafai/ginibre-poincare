module
public import GinibrePoincare.Analysis.CorrespondenceGUESplitVolume
@[expose] public section
open MeasureTheory
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def gueAuxGaussianDensity (n : ℕ) (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.exp (-(n:ℝ)/2*‖y‖^2)

theorem gueDoubledOrdered_integral_split (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ x, gueDoubledOrderedDensity n x*f (gueRealProjection n x)) =
      (∫ x,gueOrderedRawDensity n x*f x)*(∫ y,gueAuxGaussianDensity n y) := by
  have hs := (gueSplit_volume_preserving n).integral_comp
    (gueSplitMeasurableEquiv n).measurableEmbedding
    (fun p => (gueOrderedRawDensity n p.1*f p.1)*gueAuxGaussianDensity n p.2)
  have hs2 := hs.trans (integral_prod_mul (fun x => gueOrderedRawDensity n x*f x) (gueAuxGaussianDensity n))
  rw [← hs2]
  apply integral_congr_ae
  filter_upwards [] with x
  ·
    rw [gueSplitMeasurableEquiv_apply,gueDoubledOrderedDensity_split]
    unfold gueAuxGaussianDensity
    ring


theorem gueOrderedRawDensity_partition_ne_zero {n : ℕ} (hn : 0<n) :
    (∫ x,gueOrderedRawDensity n x)≠0 := by
  have h := gueDoubledOrdered_integral_split n (fun _ => 1)
  simp only [mul_one] at h
  intro hz
  rw [hz,zero_mul] at h
  exact (ne_of_gt (gueDoubledOrdered_partition_pos hn)) h

theorem gueAuxGaussianDensity_partition_ne_zero {n : ℕ} (hn : 0<n) :
    (∫ x,gueAuxGaussianDensity n x)≠0 := by
  have h := gueDoubledOrdered_integral_split n (fun _ => 1)
  simp only [mul_one] at h
  intro hz
  rw [hz,mul_zero] at h
  exact (ne_of_gt (gueDoubledOrdered_partition_pos hn)) h

/-- Exact cancellation of the auxiliary Gaussian normalization, for every real test. -/
theorem gueDoubledOrderedMeasure_real_marginal_integral {n : ℕ} (hn : 0<n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ x, f (gueRealProjection n x) ∂gueDoubledOrderedMeasure n)=
      (∫ x,gueOrderedRawDensity n x*f x)/(∫ x,gueOrderedRawDensity n x) := by
  rw [gueDoubledOrderedMeasure_integral,gueDoubledOrdered_integral_split]
  have hp := gueDoubledOrdered_integral_split n (fun _ => 1)
  simp only [mul_one] at hp
  rw [hp]
  field_simp [gueAuxGaussianDensity_partition_ne_zero hn]

#print axioms gueDoubledOrderedMeasure_real_marginal_integral

#print axioms gueDoubledOrdered_integral_split
end
end GinibrePoincare
