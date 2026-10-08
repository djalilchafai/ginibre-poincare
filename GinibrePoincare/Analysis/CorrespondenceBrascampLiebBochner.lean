module
public import GinibrePoincare.Analysis.CorrespondenceBrascampLiebAdjoint
@[expose] public section
open MeasureTheory Measure
open scoped ContDiff BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]

/-- Every pair of directions in the actual real weighted Bochner identity.
Summing these equalities over an orthonormal basis gives the full identity. -/
theorem correspondenceBrascampLieb_bochner_pair
    (W f : E → ℝ) (v w : E) (hW : ContDiff ℝ 2 W)
    (hf : ContDiff ℝ 3 f) (hc : HasCompactSupport f) :
    (∫ x, correspondenceBrascampLiebAdjoint W (bakryEmeryGibbsDirectional f v) v x *
      correspondenceBrascampLiebAdjoint W (bakryEmeryGibbsDirectional f w) w x *
      bakryEmeryGibbsWeight W x) =
    (∫ x, bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional f v) w x ^ 2 *
      bakryEmeryGibbsWeight W x) +
    ∫ x, bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional W v) w x *
      bakryEmeryGibbsDirectional f v x * bakryEmeryGibbsDirectional f w x *
      bakryEmeryGibbsWeight W x := by
  have hv : ContDiff ℝ 2 (bakryEmeryGibbsDirectional f v) :=
    correspondenceBrascampLieb_direction_contDiff (m := 2) hf v
  have hw : ContDiff ℝ 2 (bakryEmeryGibbsDirectional f w) :=
    correspondenceBrascampLieb_direction_contDiff (m := 2) hf w
  rw [correspondenceBrascampLieb_adjoint_integral W
    (bakryEmeryGibbsDirectional f v) (bakryEmeryGibbsDirectional f w) v w
    hW hv (hw.of_le (by norm_num)) (hc.fderiv_apply ℝ v) (hc.fderiv_apply ℝ w)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← congrFun (correspondenceBrascampLieb_direction_commute
    (hf.of_le (show (2 : ℕ∞ω) ≤ 3 by norm_num)) v w) x]
  ring

theorem correspondenceBrascampLieb_bochner_sum
    {ι : Type*} [Fintype ι] (W f : E → ℝ) (b : ι → E)
    (hW : ContDiff ℝ 2 W) (hf : ContDiff ℝ 3 f) (hc : HasCompactSupport f) :
    (∑ i, ∑ j, ∫ x,
      correspondenceBrascampLiebAdjoint W (bakryEmeryGibbsDirectional f (b i)) (b i) x *
      correspondenceBrascampLiebAdjoint W (bakryEmeryGibbsDirectional f (b j)) (b j) x *
      bakryEmeryGibbsWeight W x) =
    (∑ i, ∑ j, ∫ x,
      bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional f (b i)) (b j) x ^ 2 *
      bakryEmeryGibbsWeight W x) +
    ∑ i, ∑ j, ∫ x,
      bakryEmeryGibbsDirectional (bakryEmeryGibbsDirectional W (b i)) (b j) x *
      bakryEmeryGibbsDirectional f (b i) x * bakryEmeryGibbsDirectional f (b j) x *
      bakryEmeryGibbsWeight W x := by
  simp_rw [correspondenceBrascampLieb_bochner_pair W f _ _ hW hf hc]
  simp only [Finset.sum_add_distrib]

#print axioms correspondenceBrascampLieb_bochner_sum
#print axioms correspondenceBrascampLieb_bochner_pair
end
end GinibrePoincare
