module

public import GinibrePoincare.Analysis.NonQuadraticProductTensorMollification
public import GinibrePoincare.Analysis.NonQuadraticL2KernelIntegral

@[expose] public section

/-! # Concrete weighted separated convolution representatives -/
open MeasureTheory MeasureTheory.Measure Filter
open scoped Topology InnerProductSpace
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

theorem weightedTranslatedProduct_coeFn
    (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (φ ψ : ℂ → ℂ) (hφ : Continuous φ) (hψ : Continuous ψ)
    (hcφ : HasCompactSupport φ) (hcψ : HasCompactSupport ψ) (a : ℂ × ℂ) (c : ℂ) :
    ((c • l2ProductVector
      (planarWeightedTranslateL2 n V hV φ hφ hcφ a.1)
      (planarWeightedTranslateL2 n V hV ψ hψ hcψ a.2) : Lp ℂ 2 ((volume : Measure ℂ).prod volume)) : ℂ × ℂ → ℂ)
      =ᵐ[(volume : Measure ℂ).prod volume]
      (fun x => (c * (φ (x.1 - a.1) * ψ (x.2 - a.2))) *
        ((planarPotentialHalfWeight n V x.1 : ℂ) * planarPotentialHalfWeight n V x.2)) := by
  let u := planarWeightedTranslateL2 n V hV φ hφ hcφ a.1
  let v := planarWeightedTranslateL2 n V hV ψ hψ hcψ a.2
  have hu := (quasiMeasurePreserving_fst (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℂ))).ae_eq_comp
    (planarWeightedTranslate_memLp n V hV φ hφ hcφ a.1).coeFn_toLp
  have hv := (quasiMeasurePreserving_snd (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℂ))).ae_eq_comp
    (planarWeightedTranslate_memLp n V hV ψ hψ hcψ a.2).coeFn_toLp
  filter_upwards [Lp.coeFn_smul c (l2ProductVector u v), l2ProductVector_coeFn u v, hu, hv]
    with x hs hp hx hy
  change (c • l2ProductVector u v) x = _
  rw [hs]
  change c * (l2ProductVector u v) x = _
  rw [hp]
  change u x.1 = φ (x.1 - a.1) * (planarPotentialHalfWeight n V x.1 : ℂ) at hx
  change v x.2 = ψ (x.2 - a.2) * (planarPotentialHalfWeight n V x.2 : ℂ) at hy
  rw [hx, hy]
  ring

/-- The genuine Bochner average of weighted translated separated kernels
has the actual scalar separated convolution as its representative. -/
theorem weightedTranslatedProduct_integral_ae
    (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (φ ψ : ℂ → ℂ) (hφ : Continuous φ) (hψ : Continuous ψ)
    (hcφ : HasCompactSupport φ) (hcψ : HasCompactSupport ψ)
    (f : ℂ × ℂ → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    (((∫ a : ℂ × ℂ, f a • l2ProductVector
      (planarWeightedTranslateL2 n V hV φ hφ hcφ a.1)
      (planarWeightedTranslateL2 n V hV ψ hψ hcψ a.2)
      ∂((volume : Measure ℂ).prod volume)) :
      Lp ℂ 2 ((volume : Measure ℂ).prod volume)) : ℂ × ℂ → ℂ)
      =ᵐ[(volume : Measure ℂ).prod volume]
      (fun x => (∫ a : ℂ × ℂ, f a * (φ (x.1 - a.1) * ψ (x.2 - a.2))
        ∂((volume : Measure ℂ).prod volume)) *
        ((planarPotentialHalfWeight n V x.1 : ℂ) * planarPotentialHalfWeight n V x.2)) := by
  apply productL2_weighted_translated_kernel_integral_ae f
    (fun x => φ x.1 * ψ x.2)
    (fun x => (planarPotentialHalfWeight n V x.1 : ℂ) * planarPotentialHalfWeight n V x.2)
    hf ((hφ.comp continuous_fst).mul (hψ.comp continuous_snd))
  · unfold planarPotentialHalfWeight
    fun_prop
  · exact hfc
  · exact separatedPlanarKernel_hasCompactSupport φ ψ hcφ hcψ
  · exact (hf.smul (l2ProductVector_continuous.comp
      (((planarWeightedTranslateL2_continuous n V hV φ hφ hcφ).comp continuous_fst).prodMk
        ((planarWeightedTranslateL2_continuous n V hV ψ hψ hcψ).comp continuous_snd)))).integrable_of_hasCompactSupport hfc.smul_right
  · intro a
    exact weightedTranslatedProduct_coeFn n V hV φ ψ hφ hψ hcφ hcψ a (f a)
end
end GinibrePoincare
