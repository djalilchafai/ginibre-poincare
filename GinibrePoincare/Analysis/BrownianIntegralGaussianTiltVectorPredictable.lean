module

public import GinibrePoincare.Analysis.BrownianIntegralGaussianTiltVector
public import GinibrePoincare.Analysis.BrownianAugmentedFreshIncrement

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem gaussianVectorExponentialTilt_product_lintegral {α ι : Type*}
    [MeasurableSpace α] [Fintype ι] (μ : Measure α) [SFinite μ]
    (H : α → ι → ℝ) (Z : α → ℝ≥0∞) (hH : Measurable H) (hZ : Measurable Z) (v : ℝ≥0) :
    (∫⁻ z, Z z.1*ENNReal.ofReal (gaussianVectorExponentialTilt (H z.1) v z.2)
      ∂μ.prod (Measure.pi (fun _ : ι => gaussianReal 0 v))) = ∫⁻ a, Z a ∂μ := by
  classical
  rw [lintegral_prod]
  · congr 1
    funext a
    simp only [Prod.fst,Prod.snd]
    rw [lintegral_const_mul _ (by unfold gaussianVectorExponentialTilt gaussianExponentialTilt; fun_prop),
      gaussianVectorExponentialTilt_lintegral,mul_one]
  · unfold gaussianVectorExponentialTilt gaussianExponentialTilt
    fun_prop

theorem gaussianVectorExponentialTilt_product_lintegral_sq {α ι : Type*}
    [MeasurableSpace α] [Fintype ι] (μ : Measure α) [SFinite μ]
    (H : α → ι → ℝ) (Z : α → ℝ≥0∞) (hH : Measurable H) (hZ : Measurable Z) (v : ℝ≥0) :
    (∫⁻ z, Z z.1*ENNReal.ofReal (gaussianVectorExponentialTilt (H z.1) v z.2)^2
      ∂μ.prod (Measure.pi (fun _ : ι => gaussianReal 0 v))) =
      ∫⁻ a, Z a*ENNReal.ofReal (Real.exp ((∑ i, (H a i)^2)*(v : ℝ))) ∂μ := by
  classical
  rw [lintegral_prod]
  · congr 1
    funext a
    simp only [Prod.fst,Prod.snd]
    rw [lintegral_const_mul _ (by unfold gaussianVectorExponentialTilt gaussianExponentialTilt; fun_prop),
      gaussianVectorExponentialTilt_lintegral_sq]
  · unfold gaussianVectorExponentialTilt gaussianExponentialTilt
    fun_prop

theorem gaussianVectorPredictableTilt_lintegral {Ω α ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → α) (X : Ω → ι → ℝ)
    (hY : AEMeasurable Y P) (v : ℝ≥0)
    (hX : HasLaw X (Measure.pi (fun _ : ι => gaussianReal 0 v)) P)
    (hind : IndepFun Y X P) (H : α → ι → ℝ) (Z : α → ℝ≥0∞)
    (hH : Measurable H) (hZ : Measurable Z) :
    (∫⁻ ω, Z (Y ω)*ENNReal.ofReal (gaussianVectorExponentialTilt (H (Y ω)) v (X ω)) ∂P) =
      ∫⁻ ω, Z (Y ω) ∂P := by
  classical
  let μ := P.map Y
  have hYL : HasLaw Y μ P := ⟨hY,rfl⟩
  have hpair := IndepFun.hasLaw_prod hYL hX hind
  have hm : Measurable (fun z : α×(ι→ℝ) => Z z.1*
      ENNReal.ofReal (gaussianVectorExponentialTilt (H z.1) v z.2)) := by
    unfold gaussianVectorExponentialTilt gaussianExponentialTilt
    fun_prop
  have hh := hpair.lintegral_comp hm.aemeasurable
  simp only [Prod.fst,Prod.snd] at hh
  rw [gaussianVectorExponentialTilt_product_lintegral μ H Z hH hZ v] at hh
  exact hh.trans (hYL.lintegral_comp hZ.aemeasurable).symm

theorem gaussianVectorPredictableTilt_lintegral_sq {Ω α ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → α) (X : Ω → ι → ℝ)
    (hY : AEMeasurable Y P) (v : ℝ≥0)
    (hX : HasLaw X (Measure.pi (fun _ : ι => gaussianReal 0 v)) P)
    (hind : IndepFun Y X P) (H : α → ι → ℝ) (Z : α → ℝ≥0∞)
    (hH : Measurable H) (hZ : Measurable Z) :
    (∫⁻ ω, Z (Y ω)*ENNReal.ofReal (gaussianVectorExponentialTilt (H (Y ω)) v (X ω))^2 ∂P) =
      ∫⁻ ω, Z (Y ω)*ENNReal.ofReal (Real.exp ((∑ i, (H (Y ω) i)^2)*(v : ℝ))) ∂P := by
  classical
  let μ := P.map Y
  have hYL : HasLaw Y μ P := ⟨hY,rfl⟩
  have hpair := IndepFun.hasLaw_prod hYL hX hind
  have hm : Measurable (fun z : α×(ι→ℝ) => Z z.1*
      ENNReal.ofReal (gaussianVectorExponentialTilt (H z.1) v z.2)^2) := by
    unfold gaussianVectorExponentialTilt gaussianExponentialTilt
    fun_prop
  have hh := hpair.lintegral_comp hm.aemeasurable
  simp only [Prod.fst,Prod.snd] at hh
  rw [gaussianVectorExponentialTilt_product_lintegral_sq μ H Z hH hZ v] at hh
  exact hh.trans (hYL.lintegral_comp (by fun_prop)).symm

end
end GinibrePoincare
