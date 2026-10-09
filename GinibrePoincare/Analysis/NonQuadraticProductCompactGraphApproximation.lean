module

public import GinibrePoincare.Analysis.NonQuadraticProductSeparatedDerivatives
public import GinibrePoincare.Analysis.NonQuadraticProductTensorMollification
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! # Genuine normalized separated cores for the full compact product derivative graph -/
open MeasureTheory Filter
open scoped Topology ContDiff TensorProduct
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

def planarNormalizedBumpTest (φ : ContDiffBump (0 : ℂ)) : PlanarComplexCompactTest :=
  ⟨fun x => (φ.normed volume x : ℂ), Complex.ofRealCLM.contDiff.comp φ.contDiff_normed,
    φ.hasCompactSupport_normed.comp_left (g := Complex.ofReal) Complex.ofReal_zero⟩

def planarProductCompactGraphAverage (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (φ ψ : ContDiffBump (0 : ℂ)) (f : ℂ × ℂ → ℂ) : PlanarProductDbarGraphSpace :=
  ∫ a, f a • planarProductDbarGraphMap n V hV
    (planarComplexTestTranslate (planarNormalizedBumpTest φ) a.1 ⊗ₜ[ℂ]
      planarComplexTestTranslate (planarNormalizedBumpTest ψ) a.2)
    ∂((volume : Measure ℂ).prod (volume : Measure ℂ))

theorem planarProductCompactGraphAverage_mem (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (φ ψ : ContDiffBump (0 : ℂ)) (f : ℂ × ℂ → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) :
    planarProductCompactGraphAverage n V hV φ ψ f ∈ planarProductDbarClosedGraph n V hV :=
  planarProductTranslatedTensorGraph_integral_mem n V hV _ _ f hf hc

theorem planarProductCompactGraphAverage_value (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (φ ψ : ContDiffBump (0 : ℂ)) (f : ℂ × ℂ → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) :
    (planarProductCompactGraphAverage n V hV φ ψ f).1 = weightedProductBumpAverage n V hV φ ψ f := by
  unfold planarProductCompactGraphAverage
  rw [fst_integral (planarProductTranslatedTensorGraph_integrable n V hV _ _ f hf hc)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro a
  simp only [Prod.smul_fst, planarProductDbarGraphMap, LinearMap.prod_apply, Function.prod_apply,
    Function.comp_apply, planarProductWeightedValue, LinearMap.comp_apply, TensorProduct.map_tmul,
    l2ProductTensorMap_tmul, planarComplexTestTranslate_weightedValue]
  rfl
theorem planarProductCompactGraphAverage_left_coeFn
    (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (φ ψ : ContDiffBump (0 : ℂ)) (f : ℂ × ℂ → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) :
    ((planarProductCompactGraphAverage n V hV φ ψ f).2.1 : ℂ × ℂ → ℂ)
      =ᵐ[(volume : Measure ℂ).prod (volume : Measure ℂ)]
      (fun x => (∫ a, f a * (planarDbar (planarNormalizedBumpTest φ) (x.1-a.1) *
        (planarNormalizedBumpTest ψ) (x.2-a.2))
        ∂((volume : Measure ℂ).prod (volume : Measure ℂ))) * productPotentialHalfWeight n V x) := by
  have hi := planarProductTranslatedTensorGraph_integrable n V hV
    (planarNormalizedBumpTest φ) (planarNormalizedBumpTest ψ) f hf hc
  have he := weightedTranslatedProduct_integral_ae n V hV
    (planarDbar (planarNormalizedBumpTest φ)) (planarNormalizedBumpTest ψ)
    (planarComplexCompactTest_dbar_continuous _) (planarNormalizedBumpTest ψ).property.1.continuous
    (planarComplexCompactTest_dbar_compact _) (planarNormalizedBumpTest ψ).property.2 f hf hc
  have hcoord : (planarProductCompactGraphAverage n V hV φ ψ f).2.1 =
      ∫ a, f a • l2ProductVector
        (planarWeightedTranslateL2 n V hV (planarDbar (planarNormalizedBumpTest φ))
          (planarComplexCompactTest_dbar_continuous _) (planarComplexCompactTest_dbar_compact _) a.1)
        (planarWeightedTranslateL2 n V hV (planarNormalizedBumpTest ψ)
          (planarNormalizedBumpTest ψ).property.1.continuous (planarNormalizedBumpTest ψ).property.2 a.2)
        ∂((volume : Measure ℂ).prod (volume : Measure ℂ)) := by
    unfold planarProductCompactGraphAverage
    rw [snd_integral hi, fst_integral hi.snd]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro a
    simp only [Prod.smul_snd, Prod.smul_fst, planarProductDbarGraphMap, LinearMap.prod_apply,
      Function.prod_apply, Function.comp_apply, planarProductWeightedDbarLeft, LinearMap.comp_apply,
      TensorProduct.map_tmul, l2ProductTensorMap_tmul,
      planarComplexTestTranslate_weightedValue, planarComplexTestTranslate_weightedDbar]
  rw [hcoord]
  exact he

theorem planarProductCompactGraphAverage_right_coeFn
    (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (φ ψ : ContDiffBump (0 : ℂ)) (f : ℂ × ℂ → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) :
    ((planarProductCompactGraphAverage n V hV φ ψ f).2.2 : ℂ × ℂ → ℂ)
      =ᵐ[(volume : Measure ℂ).prod (volume : Measure ℂ)]
      (fun x => (∫ a, f a * ((planarNormalizedBumpTest φ) (x.1-a.1) *
        planarDbar (planarNormalizedBumpTest ψ) (x.2-a.2))
        ∂((volume : Measure ℂ).prod (volume : Measure ℂ))) * productPotentialHalfWeight n V x) := by
  have hi := planarProductTranslatedTensorGraph_integrable n V hV
    (planarNormalizedBumpTest φ) (planarNormalizedBumpTest ψ) f hf hc
  have he := weightedTranslatedProduct_integral_ae n V hV
    (planarNormalizedBumpTest φ) (planarDbar (planarNormalizedBumpTest ψ))
    (planarNormalizedBumpTest φ).property.1.continuous (planarComplexCompactTest_dbar_continuous _)
    (planarNormalizedBumpTest φ).property.2 (planarComplexCompactTest_dbar_compact _) f hf hc
  have hcoord : (planarProductCompactGraphAverage n V hV φ ψ f).2.2 =
      ∫ a, f a • l2ProductVector
        (planarWeightedTranslateL2 n V hV (planarNormalizedBumpTest φ)
          (planarNormalizedBumpTest φ).property.1.continuous (planarNormalizedBumpTest φ).property.2 a.1)
        (planarWeightedTranslateL2 n V hV (planarDbar (planarNormalizedBumpTest ψ))
          (planarComplexCompactTest_dbar_continuous _) (planarComplexCompactTest_dbar_compact _) a.2)
        ∂((volume : Measure ℂ).prod (volume : Measure ℂ)) := by
    unfold planarProductCompactGraphAverage
    rw [snd_integral hi, snd_integral hi.snd]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro a
    simp only [Prod.smul_snd, planarProductDbarGraphMap, LinearMap.prod_apply,
      Function.prod_apply, planarProductWeightedDbarRight, LinearMap.comp_apply,
      TensorProduct.map_tmul, l2ProductTensorMap_tmul,
      planarComplexTestTranslate_weightedValue, planarComplexTestTranslate_weightedDbar]
  rw [hcoord]
  exact he

theorem productSeparatedDbarLeft_convolution_transfer
    (f : ℂ × ℂ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (φ ψ : PlanarComplexCompactTest) (x : ℂ × ℂ) :
    (∫ a, f a * (planarDbar φ (x.1-a.1) * ψ (x.2-a.2))
      ∂((volume : Measure ℂ).prod (volume : Measure ℂ))) =
      ∫ a, productDbarLeft f a * (φ (x.1-a.1) * ψ (x.2-a.2))
      ∂((volume : Measure ℂ).prod (volume : Measure ℂ)) := by
  let k := fun p : ℂ × ℂ => φ p.1 * ψ p.2
  have hk : ContDiff ℝ 1 k :=
    ((φ.property.1.of_le (by norm_num)).comp contDiff_fst).mul
      ((ψ.property.1.of_le (by norm_num)).comp contDiff_snd)
  have hkc : HasCompactSupport k := separatedPlanarKernel_hasCompactSupport φ ψ φ.property.2 ψ.property.2
  have he := productComplexDbar_convolution_transfer f k hf hk hc hkc (1, 0) (Complex.I, 0) x
  change (∫ a, f a * productDbarLeft k (x-a)
      ∂((volume : Measure ℂ).prod (volume : Measure ℂ))) =
    ∫ a, productDbarLeft f a * k (x-a)
      ∂((volume : Measure ℂ).prod (volume : Measure ℂ)) at he
  dsimp only [k] at he
  simp_rw [productDbarLeft_separated φ ψ (φ.property.1.differentiable (by norm_num))
    (ψ.property.1.differentiable (by norm_num))] at he
  exact he

theorem productSeparatedDbarRight_convolution_transfer
    (f : ℂ × ℂ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (φ ψ : PlanarComplexCompactTest) (x : ℂ × ℂ) :
    (∫ a, f a * (φ (x.1-a.1) * planarDbar ψ (x.2-a.2))
      ∂((volume : Measure ℂ).prod (volume : Measure ℂ))) =
      ∫ a, productDbarRight f a * (φ (x.1-a.1) * ψ (x.2-a.2))
      ∂((volume : Measure ℂ).prod (volume : Measure ℂ)) := by
  let k := fun p : ℂ × ℂ => φ p.1 * ψ p.2
  have hk : ContDiff ℝ 1 k :=
    ((φ.property.1.of_le (by norm_num)).comp contDiff_fst).mul
      ((ψ.property.1.of_le (by norm_num)).comp contDiff_snd)
  have hkc : HasCompactSupport k := separatedPlanarKernel_hasCompactSupport φ ψ φ.property.2 ψ.property.2
  have he := productComplexDbar_convolution_transfer f k hf hk hc hkc (0, 1) (0, Complex.I) x
  change (∫ a, f a * productDbarRight k (x-a)
      ∂((volume : Measure ℂ).prod (volume : Measure ℂ))) =
    ∫ a, productDbarRight f a * k (x-a)
      ∂((volume : Measure ℂ).prod (volume : Measure ℂ)) at he
  dsimp only [k] at he
  simp_rw [productDbarRight_separated φ ψ (φ.property.1.differentiable (by norm_num))
    (ψ.property.1.differentiable (by norm_num))] at he
  exact he

theorem planarProductCompactGraphAverage_left
    (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (φ ψ : ContDiffBump (0 : ℂ)) (f : ℂ × ℂ → ℂ)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    (planarProductCompactGraphAverage n V hV φ ψ f).2.1 =
      weightedProductBumpAverage n V hV φ ψ (productDbarLeft f) := by
  have hd : Continuous (productDbarLeft f) := productComplexDbar_continuous _ _ f hf
  have hdc : HasCompactSupport (productDbarLeft f) := productComplexDbar_compact _ _ f hc
  apply Lp.ext
  filter_upwards [planarProductCompactGraphAverage_left_coeFn n V hV φ ψ f hf.continuous hc,
    weightedProductBumpAverage_coeFn n V hV φ ψ (productDbarLeft f) hd hdc] with x hl hr
  rw [hl, hr, productSeparatedDbarLeft_convolution_transfer f hf hc
    (planarNormalizedBumpTest φ) (planarNormalizedBumpTest ψ) x]
  apply congrArg (fun c : ℂ => c * productPotentialHalfWeight n V x)
  apply integral_congr_ae
  apply Eventually.of_forall
  intro a
  change productDbarLeft f a * ((φ.normed volume (x.1-a.1) : ℂ) *
    (ψ.normed volume (x.2-a.2) : ℂ)) =
    productDbarLeft f a * ((φ.normed volume (x.1-a.1) * ψ.normed volume (x.2-a.2) : ℝ) : ℂ)
  rw [Complex.ofReal_mul]

theorem planarProductCompactGraphAverage_right
    (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (φ ψ : ContDiffBump (0 : ℂ)) (f : ℂ × ℂ → ℂ)
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    (planarProductCompactGraphAverage n V hV φ ψ f).2.2 =
      weightedProductBumpAverage n V hV φ ψ (productDbarRight f) := by
  have hd : Continuous (productDbarRight f) := productComplexDbar_continuous _ _ f hf
  have hdc : HasCompactSupport (productDbarRight f) := productComplexDbar_compact _ _ f hc
  apply Lp.ext
  filter_upwards [planarProductCompactGraphAverage_right_coeFn n V hV φ ψ f hf.continuous hc,
    weightedProductBumpAverage_coeFn n V hV φ ψ (productDbarRight f) hd hdc] with x hl hr
  rw [hl, hr, productSeparatedDbarRight_convolution_transfer f hf hc
    (planarNormalizedBumpTest φ) (planarNormalizedBumpTest ψ) x]
  apply congrArg (fun c : ℂ => c * productPotentialHalfWeight n V x)
  apply integral_congr_ae
  apply Eventually.of_forall
  intro a
  change productDbarRight f a * ((φ.normed volume (x.1-a.1) : ℂ) *
    (ψ.normed volume (x.2-a.2) : ℂ)) =
    productDbarRight f a * ((φ.normed volume (x.1-a.1) * ψ.normed volume (x.2-a.2) : ℝ) : ℂ)
  rw [Complex.ofReal_mul]

def productCompactWeightedL2 (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (f : ℂ × ℂ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) : PlanarProductLebesgueL2 :=
  productCompactFunctionL2 (fun x => f x * productPotentialHalfWeight n V x)
    (hf.mul (productPotentialHalfWeight_continuous n V hV)) hc.mul_right

def productCompactWeightedDbarGraph (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (f : ℂ × ℂ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) : PlanarProductDbarGraphSpace :=
  (productCompactWeightedL2 n V hV f hf.continuous hc,
    (productCompactWeightedL2 n V hV (productDbarLeft f)
      (productComplexDbar_continuous _ _ f hf) (productComplexDbar_compact _ _ f hc),
    productCompactWeightedL2 n V hV (productDbarRight f)
      (productComplexDbar_continuous _ _ f hf) (productComplexDbar_compact _ _ f hc)))

/-- Genuine separated compact tensor graph averages approximate every
full compact C¹ function in value and both weighted Wirtinger derivatives. -/
theorem planarProductCompactGraphAverage_tendsto
    (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (φ ψ : ℕ → ContDiffBump (0 : ℂ))
    (hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0))
    (hψ : Tendsto (fun m => (ψ m).rOut) atTop (𝓝 0))
    (f : ℂ × ℂ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    Tendsto (fun m => planarProductCompactGraphAverage n V hV (φ m) (ψ m) f) atTop
      (𝓝 (productCompactWeightedDbarGraph n V hV f hf hc)) := by
  have h0 := weightedProductBumpAverage_tendsto n V hV φ ψ hφ hψ f hf.continuous hc
  have h1 := weightedProductBumpAverage_tendsto n V hV φ ψ hφ hψ (productDbarLeft f)
    (productComplexDbar_continuous _ _ f hf) (productComplexDbar_compact _ _ f hc)
  have h2 := weightedProductBumpAverage_tendsto n V hV φ ψ hφ hψ (productDbarRight f)
    (productComplexDbar_continuous _ _ f hf) (productComplexDbar_compact _ _ f hc)
  have he : (fun m => planarProductCompactGraphAverage n V hV (φ m) (ψ m) f) =
      (fun m => (weightedProductBumpAverage n V hV (φ m) (ψ m) f,
        (weightedProductBumpAverage n V hV (φ m) (ψ m) (productDbarLeft f),
        weightedProductBumpAverage n V hV (φ m) (ψ m) (productDbarRight f)))) := by
    funext m
    exact Prod.ext (planarProductCompactGraphAverage_value n V hV _ _ f hf.continuous hc)
      (Prod.ext (planarProductCompactGraphAverage_left n V hV _ _ f hf hc)
        (planarProductCompactGraphAverage_right n V hV _ _ f hf hc))
  rw [he]
  exact h0.prodMk_nhds (h1.prodMk_nhds h2)

def planarShrinkingBump (m : ℕ) : ContDiffBump (0 : ℂ) :=
  ⟨(1 / ((m : ℝ) + 1)) / 2, 1 / ((m : ℝ) + 1), by positivity, half_lt_self (by positivity)⟩

theorem planarShrinkingBump_rOut_tendsto :
    Tendsto (fun m => (planarShrinkingBump m).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Every genuine full compact C¹ product-plane function belongs to the
actual separated compact tensor value-and-derivative graph closure. -/
theorem productCompactWeightedDbarGraph_mem
    (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (f : ℂ × ℂ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    productCompactWeightedDbarGraph n V hV f hf hc ∈ planarProductDbarClosedGraph n V hV :=
  (planarProductDbarGraphMap n V hV).range.isClosed_topologicalClosure.mem_of_tendsto
    (planarProductCompactGraphAverage_tendsto n V hV planarShrinkingBump planarShrinkingBump
      planarShrinkingBump_rOut_tendsto planarShrinkingBump_rOut_tendsto f hf hc)
    (Eventually.of_forall (fun m => planarProductCompactGraphAverage_mem n V hV _ _ f hf.continuous hc))

/-- The exact two-coordinate Hörmander bound holds for every actual full
compact C¹ function, without any separated-test restriction or domain certificate. -/
theorem rhoSubharmonicPotential_product_full_compact_gap
    (n : ℕ) (hn : 0 < n) (V : ℂ → ℝ) (ρ : ℝ) (hρpos : 0 < ρ)
    (hV : ContDiff ℝ 2 V) (hρ : IsRhoSubharmonicPotential ρ V)
    (f : ℂ × ℂ → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    let x := productCompactWeightedDbarGraph n V hV.continuous f hf hc
    ‖x.1 - planarLeftBergmanProjection n V hV (planarRightBergmanProjection n V hV x.1)‖ ^ 2 ≤
      (2 / ((n : ℝ) * ρ)) * (‖x.2.1‖ ^ 2 + ‖x.2.2‖ ^ 2) :=
  rhoSubharmonicPotential_product_closed_graph_gap n hn V ρ hρpos hV hρ _
    (productCompactWeightedDbarGraph_mem n V hV.continuous f hf hc)

end
end GinibrePoincare
