module

public import GinibrePoincare.Analysis.NonQuadraticProductBergman
public import GinibrePoincare.Analysis.NonQuadraticComplexTestInverse

@[expose] public section

/-! # Actual product Hörmander estimate on the separated compact core -/
open MeasureTheory
open scoped ContDiff InnerProductSpace TensorProduct
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

abbrev PlanarProductCompactTensor := PlanarComplexCompactTest ⊗[ℂ] PlanarComplexCompactTest

def planarProductWeightedValue (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) :
    PlanarProductCompactTensor →ₗ[ℂ] PlanarProductLebesgueL2 :=
  l2ProductTensorMap.comp (TensorProduct.map (planarComplexWeightedValueL2 n V hV)
    (planarComplexWeightedValueL2 n V hV))

def planarProductWeightedDbarLeft (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) :
    PlanarProductCompactTensor →ₗ[ℂ] PlanarProductLebesgueL2 :=
  l2ProductTensorMap.comp (TensorProduct.map (planarComplexWeightedDbarL2 n V hV)
    (planarComplexWeightedValueL2 n V hV))

def planarProductWeightedDbarRight (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) :
    PlanarProductCompactTensor →ₗ[ℂ] PlanarProductLebesgueL2 :=
  l2ProductTensorMap.comp (TensorProduct.map (planarComplexWeightedValueL2 n V hV)
    (planarComplexWeightedDbarL2 n V hV))

/-- The actual bounded inverse transports to the first coordinate of every
finite separated compact test, including arbitrary sums. -/
theorem planarProductLeft_inverse_action
    (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V)
    (T : PlanarLebesgueL2 →L[ℂ] PlanarLebesgueL2)
    (hT : ∀ f : PlanarComplexCompactTest,
      T (planarComplexWeightedDbarL2 n V hV.continuous f) =
        planarComplexWeightedValueL2 n V hV.continuous f -
          planarBergmanProjection n V hV (planarComplexWeightedValueL2 n V hV.continuous f))
    (f : PlanarProductCompactTensor) :
    l2ProductLeftOperator T (planarProductWeightedDbarLeft n V hV.continuous f) =
      planarProductWeightedValue n V hV.continuous f -
        planarLeftBergmanProjection n V hV (planarProductWeightedValue n V hV.continuous f) := by
  induction f using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
    simp only [planarProductWeightedDbarLeft, planarProductWeightedValue, LinearMap.comp_apply,
      TensorProduct.map_tmul, l2ProductTensorMap_tmul, l2ProductLeftOperator_pure, hT, planarLeftBergmanProjection, l2ProductLeftOperator_pure]
    change l2ProductBilinear (_ - _) _ = _
    simp only [map_sub, LinearMap.sub_apply]
    rfl
  | add f g hf hg => simp only [map_add, hf, hg]; abel

/-- The same genuine inverse acts in the second coordinate. -/
theorem planarProductRight_inverse_action
    (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V)
    (T : PlanarLebesgueL2 →L[ℂ] PlanarLebesgueL2)
    (hT : ∀ f : PlanarComplexCompactTest,
      T (planarComplexWeightedDbarL2 n V hV.continuous f) =
        planarComplexWeightedValueL2 n V hV.continuous f -
          planarBergmanProjection n V hV (planarComplexWeightedValueL2 n V hV.continuous f))
    (f : PlanarProductCompactTensor) :
    l2ProductRightOperator T (planarProductWeightedDbarRight n V hV.continuous f) =
      planarProductWeightedValue n V hV.continuous f -
        planarRightBergmanProjection n V hV (planarProductWeightedValue n V hV.continuous f) := by
  induction f using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
    simp only [planarProductWeightedDbarRight, planarProductWeightedValue, LinearMap.comp_apply,
      TensorProduct.map_tmul, l2ProductTensorMap_tmul, l2ProductRightOperator_pure, hT, planarRightBergmanProjection, l2ProductRightOperator_pure]
    change l2ProductBilinear _ (_ - _) = _
    rw [map_sub]
    rfl
  | add f g hf hg => simp only [map_add, hf, hg]; abel
/-- Genuine two-coordinate Hörmander bound with the exact scalar constant,
for every finite sum in the separated compact C² core. -/
theorem rhoSubharmonicPotential_product_compact_tensor_gap
    (n : ℕ) (hn : 0 < n) (V : ℂ → ℝ) (ρ : ℝ) (hρpos : 0 < ρ)
    (hV : ContDiff ℝ 2 V) (hρ : IsRhoSubharmonicPotential ρ V)
    (f : PlanarProductCompactTensor) :
    let F := planarProductWeightedValue n V hV.continuous f
    ‖F - planarLeftBergmanProjection n V hV (planarRightBergmanProjection n V hV F)‖ ^ 2 ≤
      (2 / ((n : ℝ) * ρ)) *
        (‖planarProductWeightedDbarLeft n V hV.continuous f‖ ^ 2 +
          ‖planarProductWeightedDbarRight n V hV.continuous f‖ ^ 2) := by
  obtain ⟨T, hnorm, hT⟩ := rhoSubharmonicPotential_exists_bounded_dbar_inverse n hn V ρ hρpos hV hρ
  let C := 2 / ((n : ℝ) * ρ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hs := Real.sq_sqrt hC
  have bound (S : PlanarProductLebesgueL2 →L[ℂ] PlanarProductLebesgueL2)
      (hb : ‖S‖ ≤ Real.sqrt C) (G : PlanarProductLebesgueL2) : ‖S G‖ ^ 2 ≤ C * ‖G‖ ^ 2 := by
    have h := (S.le_opNorm G).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg G))
    have hh := (sq_le_sq₀ (norm_nonneg (S G))
      (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg G))).mpr h
    simpa only [mul_pow, hs] using hh
  have hl := bound (l2ProductLeftOperator T) ((l2ProductLeftOperator_norm_le T).trans hnorm)
    (planarProductWeightedDbarLeft n V hV.continuous f)
  have hr := bound (l2ProductRightOperator T) ((l2ProductRightOperator_norm_le T).trans hnorm)
    (planarProductWeightedDbarRight n V hV.continuous f)
  rw [planarProductLeft_inverse_action n V hV T hT f] at hl
  rw [planarProductRight_inverse_action n V hV T hT f] at hr
  exact (planarBergman_product_projection_error n V hV _).trans
    ((add_le_add hl hr).trans_eq (mul_add C _ _).symm)

end
end GinibrePoincare
