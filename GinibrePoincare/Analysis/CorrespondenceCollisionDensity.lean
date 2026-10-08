module

public import GinibrePoincare.Analysis.CorrespondenceCollisionVolume

@[expose] public section
namespace GinibrePoincare
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The genuine density after removing one squared collision factor. -/
def correspondenceCollisionDensityRemainder {n : ℕ} (p : VandermondePair n)
    (z : Configuration n) : ℝ :=
  (((n : ℝ) / Real.pi) ^ n) * gaussianWeight n z *
    ∏ q ∈ Finset.univ.erase p, Complex.normSq (vandermondeFactor q.val.1 q.val.2 z)

theorem correspondenceCollision_density_factor {n : ℕ} (p : VandermondePair n)
    (z : Configuration n) :
    ginibreLebesgueDensityReal n z = ‖z p.val.1 - z p.val.2‖ ^ 2 *
      correspondenceCollisionDensityRemainder p z := by
  classical
  unfold ginibreLebesgueDensityReal correspondenceCollisionDensityRemainder vandermondeWeight
  rw [vandermonde_eq_prod_pair]
  simp only [map_prod]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun q : VandermondePair n => Complex.normSq (vandermondeFactor q.val.1 q.val.2 z))
    (Finset.mem_univ p)]
  simp only [vandermondeFactor, Complex.normSq_eq_norm_sq, norm_sub_rev]
  ring

theorem correspondenceCollision_density_bound_compact {n : ℕ} (p : VandermondePair n)
    (K : Set (Configuration n)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K,
      ginibreLebesgueDensityReal n z ≤ C * ‖z p.val.1 - z p.val.2‖ ^ 2 := by
  classical
  have hg : Continuous (gaussianWeight n) := by
    unfold gaussianWeight
    exact Real.continuous_exp.comp
      (continuous_const.mul contDiff_configurationNormSq.continuous)
  have hr : Continuous (correspondenceCollisionDensityRemainder p) := by
    unfold correspondenceCollisionDensityRemainder
    apply (continuous_const.mul hg).mul
    apply continuous_finset_prod
    intro q hq
    unfold vandermondeFactor
    fun_prop
  obtain ⟨C, hC⟩ := hK.bddAbove_image hr.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro z hz
  rw [correspondenceCollision_density_factor]
  calc
    _ ≤ ‖z p.val.1 - z p.val.2‖ ^ 2 * max C 0 :=
      mul_le_mul_of_nonneg_left ((hC ⟨z, hz, rfl⟩).trans (le_max_left _ _)) (sq_nonneg _)
    _ = _ := mul_comm _ _

end
end GinibrePoincare

#print axioms GinibrePoincare.correspondenceCollision_density_factor
#print axioms GinibrePoincare.correspondenceCollision_density_bound_compact
