module

public import GinibrePoincare.Analysis.BrownianIntegralGaussianTiltVectorCentering
public import GinibrePoincare.Analysis.BrownianIntegralGaussianTiltVectorPredictable

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Every nonnegative joint past/centered-innovation test under the genuine
predictable RN tilt has the unchanged fresh Gaussian kernel. -/
theorem gaussianVectorPredictableTilt_centered_lintegral {Ω α ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → α) (X : Ω → ι → ℝ)
    (hY : AEMeasurable Y P) (v : ℝ≥0)
    (hX : HasLaw X (Measure.pi (fun _ : ι => gaussianReal 0 v)) P)
    (hind : IndepFun Y X P) (H : α → ι → ℝ) (Z : α → ℝ≥0∞)
    (hH : Measurable H) (hZ : Measurable Z)
    (F : α×(ι→ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω, Z (Y ω)*ENNReal.ofReal (gaussianVectorExponentialTilt (H (Y ω)) v (X ω))*
      F (Y ω, fun i => X ω i-H (Y ω) i*(v : ℝ)) ∂P) =
      ∫⁻ a, Z a*(∫⁻ x, F (a, x) ∂Measure.pi (fun _ : ι => gaussianReal 0 v)) ∂P.map Y := by
  classical
  let μ := P.map Y
  have hYL : HasLaw Y μ P := ⟨hY, rfl⟩
  have hpair := IndepFun.hasLaw_prod hYL hX hind
  have hm : Measurable (fun z : α×(ι→ℝ) => Z z.1*
      ENNReal.ofReal (gaussianVectorExponentialTilt (H z.1) v z.2)*
        F (z.1, fun i => z.2 i-H z.1 i*(v : ℝ))) := by
    unfold gaussianVectorExponentialTilt gaussianExponentialTilt
    fun_prop
  have hh := hpair.lintegral_comp hm.aemeasurable
  simp only [Prod.fst, Prod.snd] at hh
  rw [lintegral_prod _ hm.aemeasurable] at hh
  refine hh.trans ?_
  congr 1
  funext a
  simp only [Prod.fst, Prod.snd, mul_assoc]
  rw [lintegral_const_mul _ (by
    unfold gaussianVectorExponentialTilt gaussianExponentialTilt; fun_prop)]
  rw [gaussianVectorExponentialTilt_centered_lintegral (H a) v
    (fun x => F (a, x)) (hF.comp (measurable_const.prodMk measurable_id))]

end
end GinibrePoincare
