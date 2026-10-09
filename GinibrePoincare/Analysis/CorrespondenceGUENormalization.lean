module
public import GinibrePoincare.Analysis.CorrespondenceGUEDensityConvergence
@[expose] public section
open MeasureTheory Filter
open scoped Topology ENNReal BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def gueOrderedWitness (n : ℕ) : EuclideanSpace ℝ (Fin n×Fin 2) :=
  WithLp.toLp 2 (fun p => if p.2=0 then (p.1.val : ℝ) else 0)

theorem gueDoubledOrderedDensity_witness_pos (n : ℕ) :
    0 < gueDoubledOrderedDensity n (gueOrderedWitness n) := by
  unfold gueDoubledOrderedDensity
  apply mul_pos (Real.exp_pos _)
  apply Finset.prod_pos
  intro p hp
  have hij : p.1<p.2 := (Finset.mem_filter.mp hp).2
  have h : (0 : ℝ)<(p.2.val : ℝ)-(p.1.val : ℝ) := by
    exact sub_pos.mpr (by exact_mod_cast hij)
  change 0 < gueOrderedPairWeight ((p.2.val : ℝ)-(p.1.val : ℝ))
  rw [gueOrderedPairWeight, ite_eq_left h]
  exact sq_pos_of_pos h

theorem gueDoubledOrdered_partition_pos {n : ℕ} (hn : 0<n) :
    0 < ∫ x, gueDoubledOrderedDensity n x := by
  exact integral_pos_of_integrable_nonneg_nonzero
    (gueDoubledOrderedDensity_continuous n) (gueDoubledOrderedDensity_integrable hn)
    (gueDoubledOrderedDensity_nonneg n)
    (ne_of_gt (gueDoubledOrderedDensity_witness_pos n))


def gueDoubledOrderedMeasure (n : ℕ) : Measure (EuclideanSpace ℝ (Fin n×Fin 2)) :=
  (ENNReal.ofReal (∫ x, gueDoubledOrderedDensity n x))⁻¹ •
    volume.withDensity (fun x => ENNReal.ofReal (gueDoubledOrderedDensity n x))

theorem gueDoubledOrderedMeasure_probability {n : ℕ} (hn : 0<n) :
    IsProbabilityMeasure (gueDoubledOrderedMeasure n) := by
  constructor
  unfold gueDoubledOrderedMeasure
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal (gueDoubledOrderedDensity_integrable hn)
      (Eventually.of_forall (gueDoubledOrderedDensity_nonneg n))]
  exact ENNReal.inv_mul_cancel
    (ENNReal.ofReal_ne_zero_iff.mpr (gueDoubledOrdered_partition_pos hn)) ENNReal.ofReal_ne_top

theorem gueDoubledOrderedMeasure_integral (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n×Fin 2) → ℝ) :
    (∫ x, f x ∂gueDoubledOrderedMeasure n) =
      (∫ x, gueDoubledOrderedDensity n x*f x)/(∫ x, gueDoubledOrderedDensity n x) := by
  unfold gueDoubledOrderedMeasure
  rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul
    (μ := volume) (f := fun x => ENNReal.ofReal (gueDoubledOrderedDensity n x))
    ((gueDoubledOrderedDensity_continuous n).measurable.ennreal_ofReal)
    (Eventually.of_forall (fun x => ENNReal.ofReal_lt_top)) f]
  simp only [ENNReal.toReal_inv, ENNReal.toReal_ofReal (gueDoubledOrderedDensity_nonneg n _), smul_eq_mul]
  rw [ENNReal.toReal_ofReal (integral_nonneg (gueDoubledOrderedDensity_nonneg n))]
  ring

#print axioms gueDoubledOrderedMeasure_probability
#print axioms gueDoubledOrderedMeasure_integral

#print axioms gueDoubledOrdered_partition_pos
end
end GinibrePoincare
