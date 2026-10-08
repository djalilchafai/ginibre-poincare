module

public import GinibrePoincare.Analysis.CorrespondenceCollisionRates

@[expose] public section
namespace GinibrePoincare
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The actual product over unordered collision hyperplanes in Appendix A. -/
def correspondenceCollisionProduct (n : ℕ) (ε : ℝ) (z : Configuration n) : ℝ :=
  ∏ p : VandermondePair n, correspondenceCollisionCutoff p.val.1 p.val.2 ε z

theorem correspondenceCollisionProduct_smooth (n : ℕ) (ε : ℝ) :
    ContDiff ℝ ∞ (correspondenceCollisionProduct n ε) := by
  classical
  apply contDiff_prod
  intro p hp
  exact correspondenceCollisionCutoff_smooth p.val.1 p.val.2 ε

theorem correspondenceCollisionProduct_gradient (n : ℕ) (ε : ℝ) (z : Configuration n) :
    ginibreEuclideanGradient (correspondenceCollisionProduct n ε) z =
      ∑ p : VandermondePair n,
        (∏ q ∈ Finset.univ.erase p, correspondenceCollisionCutoff q.val.1 q.val.2 ε z) •
          ginibreEuclideanGradient (correspondenceCollisionCutoff p.val.1 p.val.2 ε) z := by
  classical
  ext k
  rw [ginibreEuclideanGradient_coordinate]
  change fderiv ℝ (fun w : Configuration n => ∏ p : VandermondePair n,
    correspondenceCollisionCutoff p.val.1 p.val.2 ε w) z (ginibreCoordinateDirection k) = _
  rw [fderiv_finsetProd (fun p _ =>
    ((correspondenceCollisionCutoff_smooth p.val.1 p.val.2 ε).differentiable (by simp)).differentiableAt)]
  simp [ginibreEuclideanGradient_coordinate]

/-- Literal squared-gradient product estimate asserted in Appendix A. -/
theorem correspondenceCollisionProduct_gradient_bound (n : ℕ) (ε : ℝ) (z : Configuration n) :
    ‖ginibreEuclideanGradient (correspondenceCollisionProduct n ε) z‖^2 ≤
      (Fintype.card (VandermondePair n) : ℝ) * ∑ p : VandermondePair n,
        ‖ginibreEuclideanGradient (correspondenceCollisionCutoff p.val.1 p.val.2 ε) z‖^2 := by
  classical
  let d (p : VandermondePair n) :=
    ginibreEuclideanGradient (correspondenceCollisionCutoff p.val.1 p.val.2 ε) z
  have hb (p : VandermondePair n) :
      ‖∏ q ∈ Finset.univ.erase p, correspondenceCollisionCutoff q.val.1 q.val.2 ε z‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg (fun q _ =>
      (correspondenceCollisionCutoff_mem_unit q.val.1 q.val.2 ε z).1))]
    exact Finset.prod_le_one₀ (fun q _ => (correspondenceCollisionCutoff_mem_unit q.val.1 q.val.2 ε z).1)
      (fun q _ => (correspondenceCollisionCutoff_mem_unit q.val.1 q.val.2 ε z).2)
  have hg : ‖ginibreEuclideanGradient (correspondenceCollisionProduct n ε) z‖ ≤ ∑ p, ‖d p‖ := by
    rw [correspondenceCollisionProduct_gradient]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro p hp
    rw [norm_smul]
    simpa [d] using mul_le_mul_of_nonneg_right (hb p) (norm_nonneg (d p))
  have hsq : ‖ginibreEuclideanGradient (correspondenceCollisionProduct n ε) z‖^2 ≤
      (∑ p, ‖d p‖)^2 :=
    (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun p hp => norm_nonneg (d p)))).mpr hg
  have hcs : (∑ p, ‖d p‖)^2 ≤
      (Fintype.card (VandermondePair n) : ℝ) * ∑ p, ‖d p‖^2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : VandermondePair n => (1 : ℝ)) (fun p => ‖d p‖)
  exact hsq.trans hcs

private theorem one_sub_prod_le_sum {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i ∧ a i ≤ 1) :
    1 - ∏ i ∈ s, a i ≤ ∑ i ∈ s, (1-a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hs : ∀ j ∈ s, 0 ≤ a j ∧ a j ≤ 1 := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have hP : ∏ j ∈ s, a j ≤ 1 := Finset.prod_le_one₀ (fun j hj => (hs j hj).1)
      (fun j hj => (hs j hj).2)
    have hai := ha i (Finset.mem_insert_self i s)
    have hih := ih hs
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    nlinarith

theorem correspondenceCollisionProduct_value_bound (n : ℕ) (ε : ℝ) (z : Configuration n) :
    |1-correspondenceCollisionProduct n ε z|^2 ≤
      (Fintype.card (VandermondePair n) : ℝ) * ∑ p : VandermondePair n,
        |1-correspondenceCollisionCutoff p.val.1 p.val.2 ε z|^2 := by
  classical
  let a (p : VandermondePair n) := correspondenceCollisionCutoff p.val.1 p.val.2 ε z
  have ha : ∀ p, 0 ≤ a p ∧ a p ≤ 1 := fun p => correspondenceCollisionCutoff_mem_unit _ _ _ _
  have hP : ∏ p, a p ≤ 1 := Finset.prod_le_one₀ (fun p hp => (ha p).1) (fun p hp => (ha p).2)
  have hs : 1 - (∏ p, a p) ≤ ∑ p, (1 - a p) :=
    one_sub_prod_le_sum Finset.univ a (fun p hp => ha p)
  have hsq := (sq_le_sq₀ (sub_nonneg.mpr hP)
    (Finset.sum_nonneg (fun p hp => sub_nonneg.mpr (ha p).2))).mpr hs
  have hcs : (∑ p, (1 - a p))^2 ≤ (Fintype.card (VandermondePair n) : ℝ) * ∑ p, (1-a p)^2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : VandermondePair n => (1 : ℝ)) (fun p => 1-a p)
  simpa only [sq_abs, correspondenceCollisionProduct, a] using hsq.trans hcs

end
end GinibrePoincare

#print axioms GinibrePoincare.correspondenceCollisionProduct_gradient_bound
#print axioms GinibrePoincare.correspondenceCollisionProduct_value_bound
