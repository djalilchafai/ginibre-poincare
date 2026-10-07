module

public import GinibrePoincare.Analysis.BrownianIntegralGaussianTiltJointLaw
public import GinibrePoincare.Analysis.BrownianIntegralGirsanovMeasure

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- The actual normalized predictable tilt preserves the past marginal and
makes the drift-corrected innovation a fresh centered Gaussian vector. -/
theorem gaussianVectorPredictableTilt_centered_fresh {Ω α ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → α) (X : Ω → ι → ℝ)
    (hY : Measurable Y) (hXm : Measurable X) (v : ℝ≥0)
    (hX : HasLaw X (Measure.pi (fun _ : ι => gaussianReal 0 v)) P)
    (hind : IndepFun Y X P) (H : α → ι → ℝ) (Z : α → ℝ≥0∞)
    (hH : Measurable H) (hZ : Measurable Z) (hZn : (∫⁻ ω, Z (Y ω) ∂P)=1) :
    let Q := P.withDensity (fun ω => Z (Y ω)*
      ENNReal.ofReal (gaussianVectorExponentialTilt (H (Y ω)) v (X ω)))
    let W := fun ω i => X ω i-H (Y ω) i*(v : ℝ)
    HasLaw Y ((P.map Y).withDensity Z) Q ∧
      HasLaw W (Measure.pi (fun _ : ι => gaussianReal 0 v)) Q ∧ IndepFun Y W Q := by
  classical
  dsimp only
  let Q := P.withDensity (fun ω => Z (Y ω)*
    ENNReal.ofReal (gaussianVectorExponentialTilt (H (Y ω)) v (X ω)))
  let ν := (P.map Y).withDensity Z
  let γ := Measure.pi (fun _ : ι => gaussianReal 0 v)
  let W := fun ω i => X ω i-H (Y ω) i*(v : ℝ)
  have hW : Measurable W := by fun_prop
  have hνn : ν Set.univ=1 := by
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,lintegral_map hZ hY]
    exact hZn
  letI : IsProbabilityMeasure ν := ⟨hνn⟩
  have hQn : Q Set.univ=1 := by
    rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
    exact (gaussianVectorPredictableTilt_lintegral P Y X hY.aemeasurable v hX hind H Z hH hZ).trans hZn
  letI : IsProbabilityMeasure Q := ⟨hQn⟩
  have hPair : HasLaw (fun ω => (Y ω,W ω)) (ν.prod γ) Q :=
    ⟨(hY.prodMk hW).aemeasurable,
      gaussianVectorPredictableTilt_centered_map P Y X hY hXm v hX hind H Z hH hZ⟩
  have hfst : HasLaw (Prod.fst : α×(ι→ℝ) → α) ν (ν.prod γ) := ⟨by fun_prop,by simp [γ]⟩
  have hsnd : HasLaw (Prod.snd : α×(ι→ℝ) → (ι→ℝ)) γ (ν.prod γ) := ⟨by fun_prop,by simp⟩
  have hYL : HasLaw Y ν Q := hfst.fun_comp hPair
  have hWL : HasLaw W γ Q := hsnd.fun_comp hPair
  exact ⟨hYL,hWL,(indepFun_iff_hasLaw_prodMk_prod hYL hWL).mpr hPair⟩

end
end GinibrePoincare
