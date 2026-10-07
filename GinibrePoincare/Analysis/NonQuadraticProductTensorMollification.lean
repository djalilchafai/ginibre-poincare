module

public import GinibrePoincare.Analysis.NonQuadraticProductDbarClosure
public import GinibrePoincare.Analysis.NonQuadraticWeightedTranslations
public import GinibrePoincare.Analysis.NonQuadraticClosedSubmoduleIntegral

@[expose] public section

/-! # Genuine translated compact tensors in the closed product derivative graph -/
open MeasureTheory Filter
open scoped Topology ContDiff TensorProduct InnerProductSpace
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

def planarComplexTestTranslate (φ : PlanarComplexCompactTest) (a : ℂ) : PlanarComplexCompactTest :=
  ⟨fun x => φ (x - a), φ.property.1.comp (contDiff_id.sub contDiff_const), by
    simpa only [sub_eq_add_neg, Function.comp_def, Homeomorph.coe_addRight] using
      φ.property.2.comp_homeomorph (Homeomorph.addRight (-a))⟩

theorem planarDbar_translate (φ : PlanarComplexCompactTest) (a x : ℂ) :
    planarDbar (planarComplexTestTranslate φ a) x = planarDbar φ (x - a) := by
  have hd : fderiv ℝ (fun y => φ (y - a)) x = fderiv ℝ φ (x - a) := by
    simpa only [Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using ((φ.property.1.differentiable (by norm_num) (x - a)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).sub_const a)).fderiv
  unfold planarDbar
  change (1 / 2 : ℂ) * ((fderiv ℝ (fun y => φ (y - a)) x) 1 +
    Complex.I * (fderiv ℝ (fun y => φ (y - a)) x) Complex.I) = _
  rw [hd]

theorem planarComplexCompactTest_dbar_continuous (φ : PlanarComplexCompactTest) : Continuous (planarDbar φ) := by
  have hd := φ.property.1.continuous_fderiv (by norm_num)
  exact continuous_const.mul ((hd.clm_apply (continuous_const (y := (1 : ℂ)))).add
    (continuous_const.mul (hd.clm_apply (continuous_const (y := Complex.I)))))

theorem planarComplexCompactTest_dbar_compact (φ : PlanarComplexCompactTest) : HasCompactSupport (planarDbar φ) :=
  ((φ.property.2.fderiv_apply ℝ 1).add
    (φ.property.2.fderiv_apply ℝ Complex.I).mul_left).mul_left

theorem planarComplexTestTranslate_weightedValue (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (φ : PlanarComplexCompactTest) (a : ℂ) :
    planarComplexWeightedValueL2 n V hV (planarComplexTestTranslate φ a) =
      planarWeightedTranslateL2 n V hV φ φ.property.1.continuous φ.property.2 a := rfl

theorem planarComplexTestTranslate_weightedDbar (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (φ : PlanarComplexCompactTest) (a : ℂ) :
    planarComplexWeightedDbarL2 n V hV (planarComplexTestTranslate φ a) =
      planarWeightedTranslateL2 n V hV (planarDbar φ)
        (planarComplexCompactTest_dbar_continuous φ) (planarComplexCompactTest_dbar_compact φ) a := by
  change planarWeightedDbarTestL2 n V hV (planarComplexTestReal (planarComplexTestTranslate φ a)) = _
  unfold planarWeightedDbarTestL2 planarWeightedTranslateL2
  apply MemLp.toLp_congr
  exact Eventually.of_forall (fun x => congrArg (fun z => z * planarPotentialHalfWeight n V x)
    (planarDbar_translate φ a x))

/-- The actual weighted value and two weighted derivative vectors of a
translated separated compact tensor vary strongly continuously. -/
theorem planarProductTranslatedTensorGraph_continuous
    (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) (φ ψ : PlanarComplexCompactTest) :
    Continuous (fun a : ℂ × ℂ => planarProductDbarGraphMap n V hV
      (planarComplexTestTranslate φ a.1 ⊗ₜ[ℂ] planarComplexTestTranslate ψ a.2)) := by
  have hv (f : PlanarComplexCompactTest) : Continuous (fun a =>
      planarComplexWeightedValueL2 n V hV (planarComplexTestTranslate f a)) := by
    simp only [planarComplexTestTranslate_weightedValue]
    exact planarWeightedTranslateL2_continuous n V hV f f.property.1.continuous f.property.2
  have hd (f : PlanarComplexCompactTest) : Continuous (fun a =>
      planarComplexWeightedDbarL2 n V hV (planarComplexTestTranslate f a)) := by
    simp only [planarComplexTestTranslate_weightedDbar]
    exact planarWeightedTranslateL2_continuous n V hV _ (planarComplexCompactTest_dbar_continuous f) (planarComplexCompactTest_dbar_compact f)
  have h1 := l2ProductVector_continuous.comp ((hv φ).comp continuous_fst |>.prodMk ((hv ψ).comp continuous_snd))
  have h2 := l2ProductVector_continuous.comp ((hd φ).comp continuous_fst |>.prodMk ((hv ψ).comp continuous_snd))
  have h3 := l2ProductVector_continuous.comp ((hv φ).comp continuous_fst |>.prodMk ((hd ψ).comp continuous_snd))
  simpa only [planarProductDbarGraphMap, LinearMap.prod_apply, Function.prod_apply, Function.comp_apply, planarProductWeightedValue,
    planarProductWeightedDbarLeft, planarProductWeightedDbarRight, LinearMap.comp_apply,
    TensorProduct.map_tmul, l2ProductTensorMap_tmul] using h1.prodMk (h2.prodMk h3)

/-- The actual compact-coefficient translated product graph is genuinely
Bochner integrable; no measurability or integrability certificate is assumed. -/
theorem planarProductTranslatedTensorGraph_integrable
    (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) (φ ψ : PlanarComplexCompactTest)
    (f : ℂ × ℂ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable (fun a => f a • planarProductDbarGraphMap n V hV
      (planarComplexTestTranslate φ a.1 ⊗ₜ[ℂ] planarComplexTestTranslate ψ a.2))
      ((volume : Measure ℂ).prod volume) :=
  (hf.smul (planarProductTranslatedTensorGraph_continuous n V hV φ ψ)).integrable_of_hasCompactSupport hc.smul_right

/-- Actual convolution graph averages belong to the genuine separated
compact tensor graph closure, by Bochner integration in that closed space. -/
theorem planarProductTranslatedTensorGraph_integral_mem
    (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) (φ ψ : PlanarComplexCompactTest)
    (f : ℂ × ℂ → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    (∫ a, f a • planarProductDbarGraphMap n V hV
      (planarComplexTestTranslate φ a.1 ⊗ₜ[ℂ] planarComplexTestTranslate ψ a.2)
      ∂((volume : Measure ℂ).prod volume)) ∈ planarProductDbarClosedGraph n V hV := by
  apply bochner_integral_mem_closed_submodule ((planarProductDbarClosedGraph n V hV).restrictScalars ℝ)
    (planarProductDbarGraphMap n V hV).range.isClosed_topologicalClosure
  · exact planarProductTranslatedTensorGraph_integrable n V hV φ ψ f hf hc
  · intro a
    exact (planarProductDbarClosedGraph n V hV).smul_mem _
      ((planarProductDbarGraphMap n V hV).range.le_topologicalClosure
        ⟨_, rfl⟩)
/-- Genuine compactly supported coefficients of translated separated tests
satisfy the exact product Hörmander inequality after Bochner convolution. -/
theorem rhoSubharmonicPotential_product_tensor_convolution_gap
    (n : ℕ) (hn : 0 < n) (V : ℂ → ℝ) (ρ : ℝ) (hρpos : 0 < ρ)
    (hV : ContDiff ℝ 2 V) (hρ : IsRhoSubharmonicPotential ρ V)
    (φ ψ : PlanarComplexCompactTest) (f : ℂ × ℂ → ℂ)
    (hf : Continuous f) (hc : HasCompactSupport f) :
    let x := ∫ a, f a • planarProductDbarGraphMap n V hV.continuous
      (planarComplexTestTranslate φ a.1 ⊗ₜ[ℂ] planarComplexTestTranslate ψ a.2)
      ∂((volume : Measure ℂ).prod volume)
    ‖x.1 - planarLeftBergmanProjection n V hV (planarRightBergmanProjection n V hV x.1)‖ ^ 2 ≤
      (2 / ((n : ℝ) * ρ)) * (‖x.2.1‖ ^ 2 + ‖x.2.2‖ ^ 2) :=
  rhoSubharmonicPotential_product_closed_graph_gap n hn V ρ hρpos hV hρ _
    (planarProductTranslatedTensorGraph_integral_mem n V hV.continuous φ ψ f hf hc)
end
end GinibrePoincare
