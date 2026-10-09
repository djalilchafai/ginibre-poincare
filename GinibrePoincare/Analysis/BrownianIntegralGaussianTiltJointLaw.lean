module

public import GinibrePoincare.Analysis.BrownianIntegralGaussianTiltConditionalCentering

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Genuine joint past/centered-innovation law under the actual predictable
Gaussian RN tilt. The past acquires only its prescribed past density. -/
theorem gaussianVectorPredictableTilt_centered_map {Ω α ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → α) (X : Ω → ι → ℝ)
    (hY : Measurable Y) (hXm : Measurable X) (v : ℝ≥0)
    (hX : HasLaw X (Measure.pi (fun _ : ι => gaussianReal 0 v)) P)
    (hind : IndepFun Y X P) (H : α → ι → ℝ) (Z : α → ℝ≥0∞)
    (hH : Measurable H) (hZ : Measurable Z) :
    (P.withDensity (fun ω => Z (Y ω)*
      ENNReal.ofReal (gaussianVectorExponentialTilt (H (Y ω)) v (X ω)))).map
        (fun ω => (Y ω, fun i => X ω i-H (Y ω) i*(v : ℝ))) =
      ((P.map Y).withDensity Z).prod (Measure.pi (fun _ : ι => gaussianReal 0 v)) := by
  classical
  let W := fun ω => (Y ω, fun i => X ω i-H (Y ω) i*(v : ℝ))
  have hW : Measurable W := by fun_prop
  ext s hs
  rw [Measure.map_apply hW hs, withDensity_apply _ (hW hs)]
  let F : α×(ι→ℝ) → ℝ≥0∞ := s.indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator hs
  have he := gaussianVectorPredictableTilt_centered_lintegral P Y X hY.aemeasurable
    v hX hind H Z hH hZ F hF
  have hpoint (ω : Ω) : Z (Y ω)*
      ENNReal.ofReal (gaussianVectorExponentialTilt (H (Y ω)) v (X ω))*F (W ω) =
      (W ⁻¹' s).indicator (fun ω => Z (Y ω)*
        ENNReal.ofReal (gaussianVectorExponentialTilt (H (Y ω)) v (X ω))) ω := by
    by_cases hw : W ω∈s <;> simp [F, Set.indicator, hw]
  change (∫⁻ ω, Z (Y ω)*ENNReal.ofReal (gaussianVectorExponentialTilt (H (Y ω)) v (X ω))*
    F (W ω) ∂P)=_ at he
  simp_rw [hpoint] at he
  rw [lintegral_indicator (hW hs)] at he
  refine he.trans ?_
  rw [Measure.prod_apply hs, lintegral_withDensity_eq_lintegral_mul _ hZ
    (measurable_measure_prodMk_left hs)]
  congr 1
  funext a
  have hfpoint : (fun x : ι→ℝ => F (a, x))=(Prod.mk a ⁻¹' s).indicator (fun _ => 1) := by
    funext x
    simp [F, Set.indicator]
  rw [hfpoint, lintegral_indicator (measurable_prodMk_left hs)]
  simp

end
end GinibrePoincare
