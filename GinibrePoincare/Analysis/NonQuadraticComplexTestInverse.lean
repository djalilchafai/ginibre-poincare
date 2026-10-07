module

public import GinibrePoincare.Analysis.NonQuadraticBergmanComplex
public import GinibrePoincare.Analysis.NonQuadraticBoundedFactorization

@[expose] public section

/-! # Complex linear compact tests and the actual bounded ∂bar inverse -/
open MeasureTheory
open scoped ContDiff InnerProductSpace
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def planarComplexCompactTestSpace : Submodule ℂ (ℂ → ℂ) where
  carrier := {f | ContDiff ℝ 2 f ∧ HasCompactSupport f}
  zero_mem' := ⟨contDiff_const, by simp [HasCompactSupport]⟩
  add_mem' := fun hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := fun c f hf => ⟨contDiff_const.smul hf.1, hf.2.smul_left⟩
abbrev PlanarComplexCompactTest := ↥planarComplexCompactTestSpace
instance : CoeFun PlanarComplexCompactTest (fun _ => ℂ → ℂ) := ⟨fun f => f.val⟩
def planarComplexTestReal (f : PlanarComplexCompactTest) : PlanarCompactTest := ⟨f.val, f.property⟩

def planarComplexWeightedValue (n : ℕ) (V : ℂ → ℝ) :
    PlanarComplexCompactTest →ₗ[ℂ] (ℂ → ℂ) where
  toFun f z := f z * planarPotentialHalfWeight n V z
  map_add' f g := by ext z; exact add_mul _ _ _
  map_smul' c f := by ext z; simp only [Pi.smul_apply, Submodule.coe_smul, smul_eq_mul, RingHom.id_apply]; exact mul_assoc _ _ _

def planarComplexWeightedDbar (n : ℕ) (V : ℂ → ℝ) :
    PlanarComplexCompactTest →ₗ[ℂ] (ℂ → ℂ) where
  toFun f z := planarDbar f z * planarPotentialHalfWeight n V z
  map_add' f g := by
    ext z
    change planarDbar (fun w => f w + g w) z * _ = _
    unfold planarDbar
    rw [fderiv_fun_add (f.property.1.differentiable (by norm_num) z)
      (g.property.1.differentiable (by norm_num) z)]
    simp only [ContinuousLinearMap.add_apply, Pi.add_apply]
    ring
  map_smul' c f := by
    ext z
    change planarDbar (fun w => c * f w) z * _ = c * _
    rw [planarDbar_const_mul _ (f.property.1.differentiable (by norm_num))]
    ring

def planarComplexTestLpLift (P : PlanarComplexCompactTest →ₗ[ℂ] (ℂ → ℂ))
    (hP : ∀ f, MemLp (P f) 2 volume) : PlanarComplexCompactTest →ₗ[ℂ] PlanarLebesgueL2 where
  toFun f := (hP f).toLp (P f)
  map_add' f g := by
    rw [← MemLp.toLp_add (hP f) (hP g)]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall (fun z => congrFun (P.map_add f g) z)
  map_smul' c f := by
    simp only [RingHom.id_apply]
    rw [← MemLp.toLp_const_smul c (hP f)]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall (fun z => congrFun (P.map_smul c f) z)

def planarComplexWeightedValueL2 (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) :
    PlanarComplexCompactTest →ₗ[ℂ] PlanarLebesgueL2 :=
  planarComplexTestLpLift (planarComplexWeightedValue n V)
    (fun f => planarWeightedTestMap_memLp n V hV (planarComplexTestReal f))

def planarComplexWeightedDbarL2 (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) :
    PlanarComplexCompactTest →ₗ[ℂ] PlanarLebesgueL2 :=
  planarComplexTestLpLift (planarComplexWeightedDbar n V)
    (fun f => planarWeightedDbarTestFunction_memLp n V hV (planarComplexTestReal f))
/-- The actual scalar Hörmander bound constructs one bounded complex
linear inverse for every compact test simultaneously. -/
theorem rhoSubharmonicPotential_exists_bounded_dbar_inverse
    (n : ℕ) (hn : 0 < n) (V : ℂ → ℝ) (ρ : ℝ) (hρpos : 0 < ρ)
    (hV : ContDiff ℝ 2 V) (hρ : IsRhoSubharmonicPotential ρ V) :
    ∃ T : PlanarLebesgueL2 →L[ℂ] PlanarLebesgueL2,
      ‖T‖ ≤ Real.sqrt (2 / ((n : ℝ) * ρ)) ∧ ∀ f : PlanarComplexCompactTest,
      T (planarComplexWeightedDbarL2 n V hV.continuous f) =
        planarComplexWeightedValueL2 n V hV.continuous f -
          planarBergmanProjection n V hV (planarComplexWeightedValueL2 n V hV.continuous f) := by
  let A := planarComplexWeightedDbarL2 n V hV.continuous
  let B := ((ContinuousLinearMap.id ℂ PlanarLebesgueL2 - planarBergmanProjection n V hV).toLinearMap).comp
    (planarComplexWeightedValueL2 n V hV.continuous)
  have hc : 0 ≤ 2 / ((n : ℝ) * ρ) := by positivity
  have hb (f : PlanarComplexCompactTest) : ‖B f‖ ≤ Real.sqrt (2 / ((n : ℝ) * ρ)) * ‖A f‖ := by
    have hs := rhoSubharmonicPotential_compact_bergman_projection_gap n hn V ρ hρpos hV hρ
      (planarComplexTestReal f)
    rw [← planarWeightedDbarTestL2_norm_sq n V hV.continuous (planarComplexTestReal f)] at hs
    change ‖B f‖ ^ 2 ≤ (2 / ((n : ℝ) * ρ)) * ‖A f‖ ^ 2 at hs
    have hsqrt := Real.sq_sqrt hc
    have hnon : 0 ≤ Real.sqrt (2 / ((n : ℝ) * ρ)) * ‖A f‖ := mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    nlinarith [norm_nonneg (B f), sq_nonneg (‖A f‖)]
  exact exists_bounded_hilbert_factor A B _ (Real.sqrt_nonneg _) hb

end
end GinibrePoincare
