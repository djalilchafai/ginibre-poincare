module

public import GinibrePoincare.Analysis.CorrespondenceCollisionProduct

@[expose] public section
namespace GinibrePoincare
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The paper's finite product has the same fourth- and second-order compact
errors, with genuine value and ordinary-gradient integrals. -/
theorem correspondenceCollisionProduct_compact_rates {n : ℕ} (hn : 0 < n)
    (K : Set (Configuration n)) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε →
      (∫ z in K, |1-correspondenceCollisionProduct n ε z|^2 ∂ginibreMeasure n) ≤ C*ε^4 ∧
      (∫ z in K, ‖ginibreEuclideanGradient (correspondenceCollisionProduct n ε) z‖^2
        ∂ginibreMeasure n) ≤ C*ε^2 := by
  classical
  letI := ginibreMeasure_isProbabilityMeasure hn
  choose C hC0 hC using fun p : VandermondePair n =>
    correspondenceCollisionCutoff_compact_rates hn p K hK
  let m : ℝ := Fintype.card (VandermondePair n)
  refine ⟨m * ∑ p, C p, mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun p hp => hC0 p)), ?_⟩
  intro ε hε
  have hc := correspondenceCollisionProduct_smooth n ε
  have hiv : IntegrableOn (fun z => |1-correspondenceCollisionProduct n ε z|^2)
      K (ginibreMeasure n) :=
    ((continuous_const.sub hc.continuous).abs.pow 2).continuousOn.integrableOn_compact hK
  have hig : IntegrableOn (fun z => ‖ginibreEuclideanGradient
      (correspondenceCollisionProduct n ε) z‖^2) K (ginibreMeasure n) :=
    ((continuous_ginibreEuclideanGradient _ hc).norm.pow 2).continuousOn.integrableOn_compact hK
  have hval (p : VandermondePair n) : IntegrableOn
      (fun z => |1-correspondenceCollisionCutoff p.val.1 p.val.2 ε z|^2) K (ginibreMeasure n) :=
    ((continuous_const.sub (correspondenceCollisionCutoff_smooth _ _ _).continuous).abs.pow 2).continuousOn.integrableOn_compact hK
  have hgrad (p : VandermondePair n) : IntegrableOn
      (fun z => ‖ginibreEuclideanGradient (correspondenceCollisionCutoff p.val.1 p.val.2 ε) z‖^2)
      K (ginibreMeasure n) :=
    ((continuous_ginibreEuclideanGradient _ (correspondenceCollisionCutoff_smooth _ _ _)).norm.pow 2).continuousOn.integrableOn_compact hK
  have hvsum : IntegrableOn (fun z => m * ∑ p : VandermondePair n,
      |1-correspondenceCollisionCutoff p.val.1 p.val.2 ε z|^2) K (ginibreMeasure n) :=
    (integrable_finsetSum _ (fun p hp => hval p)).const_mul m
  have hgsum : IntegrableOn (fun z => m * ∑ p : VandermondePair n,
      ‖ginibreEuclideanGradient (correspondenceCollisionCutoff p.val.1 p.val.2 ε) z‖^2)
      K (ginibreMeasure n) := (integrable_finsetSum _ (fun p hp => hgrad p)).const_mul m
  constructor
  · calc
      _ ≤ ∫ z in K, m * ∑ p : VandermondePair n,
          |1-correspondenceCollisionCutoff p.val.1 p.val.2 ε z|^2 ∂ginibreMeasure n :=
        setIntegral_mono_on hiv hvsum hK.measurableSet
          (fun z hz => correspondenceCollisionProduct_value_bound n ε z)
      _ = m * ∑ p : VandermondePair n, ∫ z in K,
          |1-correspondenceCollisionCutoff p.val.1 p.val.2 ε z|^2 ∂ginibreMeasure n := by
        rw [integral_const_mul, integral_finsetSum _ (fun p hp => hval p)]
      _ ≤ m * ∑ p : VandermondePair n, C p * ε^4 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun p hp => (hC p ε hε).1)) (Nat.cast_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring
  · calc
      _ ≤ ∫ z in K, m * ∑ p : VandermondePair n,
          ‖ginibreEuclideanGradient (correspondenceCollisionCutoff p.val.1 p.val.2 ε) z‖^2
          ∂ginibreMeasure n :=
        setIntegral_mono_on hig hgsum hK.measurableSet
          (fun z hz => correspondenceCollisionProduct_gradient_bound n ε z)
      _ = m * ∑ p : VandermondePair n, ∫ z in K,
          ‖ginibreEuclideanGradient (correspondenceCollisionCutoff p.val.1 p.val.2 ε) z‖^2
          ∂ginibreMeasure n := by
        rw [integral_const_mul, integral_finsetSum _ (fun p hp => hgrad p)]
      _ ≤ m * ∑ p : VandermondePair n, C p * ε^2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun p hp => (hC p ε hε).2)) (Nat.cast_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring

end
end GinibrePoincare

#print axioms GinibrePoincare.correspondenceCollisionProduct_compact_rates
