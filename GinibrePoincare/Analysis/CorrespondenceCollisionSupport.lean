module
public import GinibrePoincare.Analysis.CorrespondenceCollisionProductRates

@[expose] public section
namespace GinibrePoincare
noncomputable section
open scoped ContDiff
set_option backward.isDefEq.respectTransparency false

theorem correspondenceCollisionProduct_support_separated (n : ℕ) (ε : ℝ)
    (hε : 0 < ε) (p : VandermondePair n) :
    tsupport (correspondenceCollisionProduct n ε) ⊆
      {z | ε ≤ ‖z p.val.1-z p.val.2‖} := by
  classical
  apply closure_minimal
  · intro z hz
    by_contra h
    have he := correspondenceCollisionCutoff_zero p.val.1 p.val.2 hε z (le_of_not_ge h)
    have hp : correspondenceCollisionProduct n ε z = 0 := by
      unfold correspondenceCollisionProduct
      exact Finset.prod_eq_zero (Finset.mem_univ p) he
    exact hz hp
  · exact isClosed_le continuous_const
      ((continuous_apply p.val.1).sub (continuous_apply p.val.2)).norm

theorem correspondenceCollisionProduct_support_collisionFree (n : ℕ) (ε : ℝ)
    (hε : 0 < ε) : tsupport (correspondenceCollisionProduct n ε) ⊆
      {z | CollisionFree z} := by
  intro z hz j k he
  by_contra hjk
  rcases lt_or_gt_of_ne hjk with h|h
  · have hb := correspondenceCollisionProduct_support_separated n ε hε ⟨(j, k), h⟩ hz
    simp only [Set.mem_setOf_eq, he, sub_self, norm_zero] at hb
    linarith
  · have hb := correspondenceCollisionProduct_support_separated n ε hε ⟨(k, j), h⟩ hz
    simp only [Set.mem_setOf_eq, he, sub_self, norm_zero] at hb
    linarith

/-- The literal product cutoff gives a smooth compact test supported away from collisions. -/
theorem correspondenceCollisionProduct_compact_test (n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ContDiff ℝ ∞ (fun z => f z*correspondenceCollisionProduct n ε z) ∧
    HasCompactSupport (fun z => f z*correspondenceCollisionProduct n ε z) ∧
    tsupport (fun z => f z*correspondenceCollisionProduct n ε z) ⊆ {z | CollisionFree z} := by
  refine ⟨hf.mul (correspondenceCollisionProduct_smooth n ε), hc.mul_right,?_⟩
  exact tsupport_mul_subset_right.trans
    (correspondenceCollisionProduct_support_collisionFree n ε hε)

#print axioms correspondenceCollisionProduct_compact_test
end
end GinibrePoincare
