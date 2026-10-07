module

public import GinibrePoincare.Analysis.NonQuadraticCompactConvolutionSupport
public import GinibrePoincare.Analysis.NonQuadraticProductTensorConvolution

@[expose] public section

/-! # Genuine weighted compact separated convolution averages -/
open MeasureTheory Filter
open scoped Topology Pointwise ENNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

def productPotentialHalfWeight (n : ℕ) (V : ℂ → ℝ) (x : ℂ × ℂ) : ℂ :=
  planarPotentialHalfWeight n V x.1 * planarPotentialHalfWeight n V x.2

theorem productPotentialHalfWeight_continuous (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) :
    Continuous (productPotentialHalfWeight n V) := by
  unfold productPotentialHalfWeight planarPotentialHalfWeight
  fun_prop

private theorem complexBump_continuous (φ : ContDiffBump (0 : ℂ)) :
    Continuous (fun x => (φ.normed volume x : ℂ)) :=
  Complex.continuous_ofReal.comp φ.continuous_normed

private theorem complexBump_compact (φ : ContDiffBump (0 : ℂ)) :
    HasCompactSupport (fun x => (φ.normed volume x : ℂ)) :=
  φ.hasCompactSupport_normed.comp_left (g := Complex.ofReal) Complex.ofReal_zero

def weightedProductBumpAverage (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (φ ψ : ContDiffBump (0 : ℂ)) (f : ℂ × ℂ → ℂ) :
    Lp ℂ 2 ((volume : Measure ℂ).prod (volume : Measure ℂ)) :=
  ∫ a, f a • l2ProductVector
    (planarWeightedTranslateL2 n V hV (fun x => (φ.normed volume x : ℂ))
      (by exact complexBump_continuous φ) (by exact complexBump_compact φ) a.1)
    (planarWeightedTranslateL2 n V hV (fun x => (ψ.normed volume x : ℂ))
      (by exact complexBump_continuous ψ) (by exact complexBump_compact ψ) a.2)
    ∂((volume : Measure ℂ).prod (volume : Measure ℂ))

theorem weightedProductBumpAverage_coeFn
    (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (φ ψ : ContDiffBump (0 : ℂ)) (f : ℂ × ℂ → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) :
    (weightedProductBumpAverage n V hV φ ψ f : ℂ × ℂ → ℂ)
      =ᵐ[(volume : Measure ℂ).prod (volume : Measure ℂ)]
      (fun x => (∫ a, f a * (separatedPlanarBump φ ψ (x-a) : ℂ)
        ∂((volume : Measure ℂ).prod (volume : Measure ℂ))) * productPotentialHalfWeight n V x) := by
  have he := weightedTranslatedProduct_integral_ae n V hV
    (fun x => (φ.normed volume x : ℂ)) (fun x => (ψ.normed volume x : ℂ))
    (complexBump_continuous φ) (complexBump_continuous ψ)
    (complexBump_compact φ) (complexBump_compact ψ) f hf hc
  simpa only [weightedProductBumpAverage, productPotentialHalfWeight, separatedPlanarBump,
    Prod.fst_sub, Prod.snd_sub, Complex.ofReal_mul] using he

/-- Whole product L² smoothing can be localized to an arbitrary continuous
weight on a genuine common compact region. -/
theorem weightedProductBumpAverage_tendsto
    (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (φ ψ : ℕ → ContDiffBump (0 : ℂ))
    (hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0))
    (hψ : Tendsto (fun m => (ψ m).rOut) atTop (𝓝 0))
    (f : ℂ × ℂ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    Tendsto (fun m => weightedProductBumpAverage n V hV (φ m) (ψ m) f) atTop
      (𝓝 (productCompactFunctionL2 (fun x => f x * productPotentialHalfWeight n V x)
        (hf.mul (productPotentialHalfWeight_continuous n V hV)) hc.mul_right)) := by
  let S := tsupport f + Metric.closedBall (0 : ℂ × ℂ) 1
  have hS : IsCompact S := IsCompact.add hc (isCompact_closedBall _ _)
  let w := productPotentialHalfWeight n V
  have hw : Continuous w := productPotentialHalfWeight_continuous n V hV
  obtain ⟨T, hT⟩ := exists_compactProductL2WeightMultiplier w hw S hS
  let u := productCompactFunctionL2 f hf hc
  let uw := productCompactFunctionL2 (fun x => f x * w x) (hf.mul hw) hc.mul_right
  have hu : (u : ℂ × ℂ → ℂ) =ᵐ[(volume : Measure ℂ).prod (volume : Measure ℂ)] f :=
    (hf.memLp_of_hasCompactSupport hc).coeFn_toLp
  have huw : (uw : ℂ × ℂ → ℂ) =ᵐ[(volume : Measure ℂ).prod (volume : Measure ℂ)] (fun x => f x * w x) :=
    ((hf.mul hw).memLp_of_hasCompactSupport hc.mul_right).coeFn_toLp
  have hfS (x : ℂ × ℂ) (hx : x ∉ S) : f x = 0 := by
    by_contra h
    apply hx
    exact ⟨x, subset_closure h, 0, by simp, by simp⟩
  have hTu : T u = uw := by
    apply Lp.ext
    filter_upwards [hT u, hu, huw] with x ht hf' hw'
    rw [ht, hf', hw']
    by_cases hx : x ∈ S
    · simp only [Set.indicator_of_mem hx]
      exact mul_comm _ _
    · simp only [Set.indicator_of_notMem hx, hfS x hx, zero_mul, mul_zero]
  have hr : Tendsto (fun m => max (φ m).rOut (ψ m).rOut) atTop (𝓝 0) := by
    simpa only [max_self] using hφ.max hψ
  have hsmall : ∀ᶠ m in atTop, max (φ m).rOut (ψ m).rOut ≤ 1 :=
    ((tendsto_order.mp hr).2 1 (by norm_num)).mono (fun m hm => hm.le)
  have he : ∀ᶠ m in atTop, T (separatedL2BumpAverage (φ m) (ψ m) u) =
      weightedProductBumpAverage n V hV (φ m) (ψ m) f := by
    filter_upwards [hsmall] with m hm
    apply Lp.ext
    filter_upwards [hT (separatedL2BumpAverage (φ m) (ψ m) u),
      separatedL2BumpAverage_convolution_ae (φ m) (ψ m) f hf hc,
      weightedProductBumpAverage_coeFn n V hV (φ m) (ψ m) f hf hc] with x ht ha hw'
    rw [ht, ha, hw']
    rw [productPlane_convolution_swap]
    by_cases hx : x ∈ S
    · simp only [Set.indicator_of_mem hx]
      exact mul_comm _ _
    · have hz := separatedCompactConvolution_eq_zero_of_not_mem f (φ m) (ψ m) 1 hm x hx
      simp only [Set.indicator_of_notMem hx, hz, zero_mul, mul_zero]
  have ht := T.continuous.tendsto u |>.comp (separatedL2BumpAverage_tendsto φ ψ hφ hψ u)
  rw [hTu] at ht
  exact ht.congr' he
end
end GinibrePoincare
