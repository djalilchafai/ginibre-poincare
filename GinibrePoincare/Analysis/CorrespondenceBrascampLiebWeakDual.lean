module
public import GinibrePoincare.Analysis.CorrespondenceBrascampLiebWeakBound
public import GinibrePoincare.Analysis.CorrespondenceBrascampLiebCenter
@[expose] public section
open MeasureTheory Measure
open scoped ContDiff BigOperators Matrix
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem correspondenceBrascampLieb_weak_centered_core_bound
    (W u : E → ℝ) (G : E → ι → ℝ) (b : ι → E) (hW : ContDiff ℝ 2 W)
    [IsFiniteMeasure (correspondenceBrascampLiebMeasure W)]
    (hu : MemLp u 2 (correspondenceBrascampLiebMeasure W))
    (hG : ∀ i, CorrespondenceBrascampLiebLocallyL2 (fun x => G x i))
    (hw : CorrespondenceBrascampLiebHasWeakGradient u G b)
    (hpos : ∀ x, (correspondenceBrascampLiebHessian W b x).PosDef)
    (hE : Integrable (correspondenceBrascampLiebWeakInverseEnergy W G b)
      (correspondenceBrascampLiebMeasure W))
    (f : CorrespondenceBrascampLiebCompactTest E) :
    (inner ℝ ((correspondenceBrascampLieb_center_memLp W u hu).toLp
        (correspondenceBrascampLiebCenter W u)) (correspondenceBrascampLiebCoreL2 W b hW f))^2 ≤
    (∫ x, correspondenceBrascampLiebWeakInverseEnergy W G b x ∂correspondenceBrascampLiebMeasure W)*
      ‖correspondenceBrascampLiebCoreL2 W b hW f‖^2 := by
  let μ := correspondenceBrascampLiebMeasure W
  let L := bakryEmeryGibbsGenerator W b f.val
  have hLp : MemLp L 2 μ := correspondenceBrascampLieb_generator_memLp W f.val b hW
    (f.smooth.of_le (by norm_num)) f.compact
  have hiu : Integrable (fun x => u x*L x) μ := hu.integrable_mul hLp
  have hiL : Integrable L μ := hLp.integrable (by norm_num)
  have hstat : (∫ x, L x ∂μ) = 0 := by
    rw [correspondenceBrascampLieb_integral_density W _ hW.continuous]
    exact bakryEmeryGibbs_core_stationarity W f.val b (hW.of_le (by norm_num))
      (f.smooth.of_le (by norm_num)) f.compact
  have hcenter : (∫ x, correspondenceBrascampLiebCenter W u x*L x ∂μ) =
      ∫ x, u x*L x ∂μ := by
    unfold correspondenceBrascampLiebCenter
    simp_rw [sub_mul]
    rw [integral_sub hiu (hiL.const_mul _),integral_const_mul,hstat]
    ring
  unfold correspondenceBrascampLiebCoreL2
  rw [correspondenceBrascampLieb_toLp_inner,correspondenceBrascampLieb_toLp_norm_sq]
  rw [hcenter]
  exact correspondenceBrascampLieb_weak_compact_bound W u f.val G b hW hu hG hw hpos hE
    (f.smooth.of_le (by norm_num)) f.compact

#print axioms correspondenceBrascampLieb_weak_centered_core_bound
end
end GinibrePoincare
