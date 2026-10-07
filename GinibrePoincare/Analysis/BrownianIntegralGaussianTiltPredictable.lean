module

public import GinibrePoincare.Analysis.BrownianIntegralGaussianTiltNonnegative
public import GinibrePoincare.Analysis.GinibreStochasticAugmentedPredictableQuadratic

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000

/-- A genuine independent Gaussian innovation normalizes any nonnegative
past weight even when its tilt coefficient depends on the whole past. -/
theorem gaussianPredictableTilt_lintegral {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → α) (X : Ω → ℝ)
    (hY : AEMeasurable Y P) (v : ℝ≥0) (hX : HasLaw X (gaussianReal 0 v) P)
    (hind : IndepFun Y X P) (H : α → ℝ) (Z : α → ℝ≥0∞)
    (hH : Measurable H) (hZ : Measurable Z) :
    (∫⁻ ω, Z (Y ω)*ENNReal.ofReal (gaussianExponentialTilt (H (Y ω)) v (X ω)) ∂P) =
      ∫⁻ ω, Z (Y ω) ∂P := by
  let μ := P.map Y
  have hYL : HasLaw Y μ P := ⟨hY,rfl⟩
  have hpair := IndepFun.hasLaw_prod hYL hX hind
  have hm : Measurable (fun z : α×ℝ => Z z.1*
      ENNReal.ofReal (gaussianExponentialTilt (H z.1) v z.2)) := by
    unfold gaussianExponentialTilt
    fun_prop
  have hh := hpair.lintegral_comp hm.aemeasurable
  simp only [Prod.fst,Prod.snd] at hh
  rw [gaussianExponentialTilt_product_lintegral μ H Z hH hZ v] at hh
  exact hh.trans (hYL.lintegral_comp hZ.aemeasurable).symm

theorem gaussianPredictableTilt_lintegral_sq {Ω α : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → α) (X : Ω → ℝ)
    (hY : AEMeasurable Y P) (v : ℝ≥0) (hX : HasLaw X (gaussianReal 0 v) P)
    (hind : IndepFun Y X P) (H : α → ℝ) (Z : α → ℝ≥0∞)
    (hH : Measurable H) (hZ : Measurable Z) :
    (∫⁻ ω, Z (Y ω)*ENNReal.ofReal (gaussianExponentialTilt (H (Y ω)) v (X ω))^2 ∂P) =
      ∫⁻ ω, Z (Y ω)*ENNReal.ofReal (Real.exp ((H (Y ω))^2*(v : ℝ))) ∂P := by
  let μ := P.map Y
  have hYL : HasLaw Y μ P := ⟨hY,rfl⟩
  have hpair := IndepFun.hasLaw_prod hYL hX hind
  have hm : Measurable (fun z : α×ℝ => Z z.1*
      ENNReal.ofReal (gaussianExponentialTilt (H z.1) v z.2)^2) := by
    unfold gaussianExponentialTilt
    fun_prop
  have hh := hpair.lintegral_comp hm.aemeasurable
  simp only [Prod.fst,Prod.snd] at hh
  rw [gaussianExponentialTilt_product_lintegral_sq μ H Z hH hZ v] at hh
  exact hh.trans (hYL.lintegral_comp (by fun_prop)).symm

end
end GinibrePoincare
