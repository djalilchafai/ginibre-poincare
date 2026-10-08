module
public import GinibrePoincare.Analysis.CorrespondenceGUEOrderedDensity
@[expose] public section
open MeasureTheory Filter
open scoped ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem gueOrderedRawDensity_nonneg (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    0≤gueOrderedRawDensity n x := by
  unfold gueOrderedRawDensity gueOrderedPairWeight
  positivity

theorem gueOrderedRawDensity_integrable {n : ℕ} (hn : 0<n) :
    Integrable (gueOrderedRawDensity n) volume := by
  have hs : Integrable (fun p : EuclideanSpace ℝ (Fin n)×EuclideanSpace ℝ (Fin n) =>
      gueOrderedRawDensity n p.1*gueAuxGaussianDensity n p.2) (volume.prod volume) := by
    apply ((gueSplit_volume_preserving n).integrable_comp_emb
      (gueSplitMeasurableEquiv n).measurableEmbedding).mp
    convert gueDoubledOrderedDensity_integrable hn using 1
    funext x
    simp only [Function.comp_apply,gueSplitMeasurableEquiv_apply]
    exact (gueDoubledOrderedDensity_split n x).symm
  obtain ⟨y,hy⟩ := hs.prod_left_ae.exists
  exact (integrable_mul_const_iff (isUnit_iff_ne_zero.mpr (Real.exp_ne_zero (-(n:ℝ)/2*‖y‖^2))) (gueOrderedRawDensity n)).mp hy

theorem gueOrderedRawDensity_partition_pos {n : ℕ} (hn : 0<n) :
    0<∫x,gueOrderedRawDensity n x := by
  exact lt_of_le_of_ne (integral_nonneg (gueOrderedRawDensity_nonneg n))
    (Ne.symm (gueOrderedRawDensity_partition_ne_zero hn))

def gueOrderedMeasure (n : ℕ) : Measure (EuclideanSpace ℝ (Fin n)) :=
  (ENNReal.ofReal (∫x,gueOrderedRawDensity n x))⁻¹ •
    volume.withDensity (fun x => ENNReal.ofReal (gueOrderedRawDensity n x))

theorem gueOrderedMeasure_probability {n : ℕ} (hn : 0<n) :
    IsProbabilityMeasure (gueOrderedMeasure n) := by
  constructor
  unfold gueOrderedMeasure
  rw [Measure.smul_apply,withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal (gueOrderedRawDensity_integrable hn)
      (Eventually.of_forall (gueOrderedRawDensity_nonneg n))]
  exact ENNReal.inv_mul_cancel
    (ENNReal.ofReal_ne_zero_iff.mpr (gueOrderedRawDensity_partition_pos hn)) ENNReal.ofReal_ne_top


theorem gueOrderedRawDensity_continuous (n : ℕ) : Continuous (gueOrderedRawDensity n) := by
  unfold gueOrderedRawDensity
  apply Continuous.mul
  · fun_prop
  · apply continuous_finsetProd
    intro p hp
    apply gueOrderedPairWeight_continuous.comp
    exact ((PiLp.proj 2 (fun _ : Fin n => ℝ) p.2 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).continuous).sub
      ((PiLp.proj 2 (fun _ : Fin n => ℝ) p.1 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).continuous)

theorem gueOrderedMeasure_integral (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫x,f x ∂gueOrderedMeasure n)=
      (∫x,gueOrderedRawDensity n x*f x)/(∫x,gueOrderedRawDensity n x) := by
  unfold gueOrderedMeasure
  rw [integral_smul_measure,integral_withDensity_eq_integral_toReal_smul
    (μ := volume) (f := fun x => ENNReal.ofReal (gueOrderedRawDensity n x))
    ((gueOrderedRawDensity_continuous n).measurable.ennreal_ofReal)
    (Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)) f]
  simp only [ENNReal.toReal_inv,ENNReal.toReal_ofReal (gueOrderedRawDensity_nonneg n _),smul_eq_mul]
  rw [ENNReal.toReal_ofReal (integral_nonneg (gueOrderedRawDensity_nonneg n))]
  ring

theorem gueOrderedMeasure_real_marginal_integral {n : ℕ} (hn : 0<n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫x,f (gueRealProjection n x) ∂gueDoubledOrderedMeasure n)=(∫x,f x ∂gueOrderedMeasure n) := by
  rw [gueOrderedMeasure_integral]
  exact gueDoubledOrderedMeasure_real_marginal_integral hn f

#print axioms gueOrderedMeasure_real_marginal_integral

#print axioms gueOrderedRawDensity_integrable
#print axioms gueOrderedMeasure_probability
end
end GinibrePoincare
