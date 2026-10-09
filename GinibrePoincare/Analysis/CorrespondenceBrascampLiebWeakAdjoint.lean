module
public import GinibrePoincare.Analysis.CorrespondenceBrascampLiebWeakTests
public import GinibrePoincare.Analysis.CorrespondenceBrascampLiebDensityGenerator
@[expose] public section
open MeasureTheory Measure
open scoped ContDiff BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]

/-- Actual ordinary distributional gradients satisfy the weighted adjoint
identity internally, including C² rather than analytic potentials. -/
theorem correspondenceBrascampLieb_weak_weighted_adjoint
    (W u G : E → ℝ) (v : E) (hW : ContDiff ℝ 1 W)
    [IsFiniteMeasure (correspondenceBrascampLiebMeasure W)]
    (hu : MemLp u 2 (correspondenceBrascampLiebMeasure W))
    (hG : CorrespondenceBrascampLiebLocallyL2 G)
    (hw : CorrespondenceBrascampLiebHasWeakDerivative u G v)
    (θ : E → ℝ) (hθ : ContDiff ℝ 1 θ) (hc : HasCompactSupport θ) :
    (∫ x, G x*θ x ∂correspondenceBrascampLiebMeasure W) =
      ∫ x, u x*(bakryEmeryGibbsDirectional W v x*θ x-
        bakryEmeryGibbsDirectional θ v x) ∂correspondenceBrascampLiebMeasure W := by
  let ρ := bakryEmeryGibbsWeight W
  have hρ : ContDiff ℝ 1 ρ := Real.contDiff_exp.comp hW.neg
  have he := correspondenceBrascampLieb_weak_test_C1 W u G v hW.continuous hu hG hw
    (ρ*θ) (hρ.mul hθ) hc.mul_left
  have hder (x : E) : fderiv ℝ (ρ*θ) x v =
      ρ x*(bakryEmeryGibbsDirectional θ v x-
        bakryEmeryGibbsDirectional W v x*θ x) := by
    rw [fderiv_mul (hρ.differentiable (by norm_num) x) (hθ.differentiable (by norm_num) x)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hd := correspondenceBrascampLieb_density_derivative W hW v x
    change fderiv ℝ ρ x v = -bakryEmeryGibbsDirectional W v x*ρ x at hd
    rw [hd]
    unfold bakryEmeryGibbsDirectional
    ring
  rw [correspondenceBrascampLieb_integral_density W _ hW.continuous,
    correspondenceBrascampLieb_integral_density W _ hW.continuous]
  calc
    _ = ∫ x, (ρ*θ) x*G x := by
      apply integral_congr_ae
      exact ae_of_all volume fun x => by simp only [Pi.mul_apply]; dsimp [ρ]; ring
    _ = -(∫ x, fderiv ℝ (ρ*θ) x v*u x) := he
    _ = _ := by
      rw [← integral_neg]
      apply integral_congr_ae
      exact ae_of_all volume fun x => by
        dsimp only
        rw [hder]
        dsimp [ρ]
        ring

#print axioms correspondenceBrascampLieb_weak_weighted_adjoint
end
end GinibrePoincare
