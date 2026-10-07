module

public import GinibrePoincare.Analysis.NonQuadraticPiBergman
public import GinibrePoincare.Analysis.NonQuadraticComplexTestInverse

@[expose] public section

open MeasureTheory
open scoped ContDiff InnerProductSpace
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 30000
set_option backward.isDefEq.respectTransparency false

def planarPiPureWeightedValue {m : ℕ} (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (f : Fin (m+1) → PlanarComplexCompactTest) : PlanarPiLebesgueL2 (m+1) :=
  l2PiProductVector (fun _ => (volume : Measure ℂ)) (fun i => planarComplexWeightedValueL2 n V hV (f i))

def planarPiPureWeightedDbar {m : ℕ} (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (f : Fin (m+1) → PlanarComplexCompactTest) (i : Fin (m+1)) : PlanarPiLebesgueL2 (m+1) :=
  l2PiProductVector (fun _ => (volume : Measure ℂ))
    (Function.update (fun j => planarComplexWeightedValueL2 n V hV (f j)) i
      (planarComplexWeightedDbarL2 n V hV (f i)))

theorem planarPiPure_inverse_action {m : ℕ} (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V)
    (T : PlanarLebesgueL2 →L[ℂ] PlanarLebesgueL2)
    (hT : ∀ f : PlanarComplexCompactTest,
      T (planarComplexWeightedDbarL2 n V hV.continuous f) =
        planarComplexWeightedValueL2 n V hV.continuous f -
          planarBergmanProjection n V hV (planarComplexWeightedValueL2 n V hV.continuous f))
    (f : Fin (m+1) → PlanarComplexCompactTest) (i : Fin (m+1)) :
    l2PiCoordinateOperator (fun _ => (volume : Measure ℂ)) i T
        (planarPiPureWeightedDbar n V hV.continuous f i) =
      planarPiPureWeightedValue n V hV.continuous f -
        planarPiBergmanCoordinate n V hV i (planarPiPureWeightedValue n V hV.continuous f) := by
  let E := l2PiCoordinateEquiv (fun _ : Fin (m+1) => (volume : Measure ℂ)) i
  apply E.injective
  change E ((E).symm
    (l2ProductLeftOperator T (E (planarPiPureWeightedDbar n V hV.continuous f i)))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  dsimp [E]
  unfold planarPiPureWeightedDbar
  rw [l2PiProductVector_split, l2ProductLeftOperator_pure]
  simp only [Function.update_self]
  rw [hT, map_sub]
  change _ = E (planarPiPureWeightedValue n V hV.continuous f) -
    E ((E).symm
      (l2ProductLeftOperator (planarBergmanProjection n V hV)
        (E (planarPiPureWeightedValue n V hV.continuous f))))
  rw [LinearIsometryEquiv.apply_symm_apply]
  unfold planarPiPureWeightedValue
  rw [l2PiProductVector_split, l2ProductLeftOperator_pure]
  change l2ProductBilinear (_ - _) _ = _
  simp only [Function.update_of_ne (Fin.succAbove_ne i _)]
  rw [map_sub]
  rfl

def planarPiCoreWeightedValue {m : ℕ} (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (fs : List (ℂ × (Fin (m+1) → PlanarComplexCompactTest))) : PlanarPiLebesgueL2 (m+1) :=
  (fs.map (fun cf => cf.1 • planarPiPureWeightedValue n V hV cf.2)).sum

def planarPiCoreWeightedDbar {m : ℕ} (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (fs : List (ℂ × (Fin (m+1) → PlanarComplexCompactTest))) (i : Fin (m+1)) : PlanarPiLebesgueL2 (m+1) :=
  (fs.map (fun cf => cf.1 • planarPiPureWeightedDbar n V hV cf.2 i)).sum

theorem planarPiCore_inverse_action {m : ℕ} (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V)
    (T : PlanarLebesgueL2 →L[ℂ] PlanarLebesgueL2)
    (hT : ∀ f : PlanarComplexCompactTest,
      T (planarComplexWeightedDbarL2 n V hV.continuous f) =
        planarComplexWeightedValueL2 n V hV.continuous f -
          planarBergmanProjection n V hV (planarComplexWeightedValueL2 n V hV.continuous f))
    (fs : List (ℂ × (Fin (m+1) → PlanarComplexCompactTest))) (i : Fin (m+1)) :
    l2PiCoordinateOperator (fun _ => (volume : Measure ℂ)) i T
        (planarPiCoreWeightedDbar n V hV.continuous fs i) =
      planarPiCoreWeightedValue n V hV.continuous fs -
        planarPiBergmanCoordinate n V hV i (planarPiCoreWeightedValue n V hV.continuous fs) := by
  induction fs with
  | nil => simp [planarPiCoreWeightedDbar, planarPiCoreWeightedValue]
  | cons cf fs ih =>
    simp only [planarPiCoreWeightedDbar, planarPiCoreWeightedValue, List.map_cons, List.sum_cons,
      map_add, map_smul] at ih ⊢
    rw [planarPiPure_inverse_action n V hV T hT, ih, smul_sub]
    abel

/-- The exact arbitrary-dimensional Hörmander bound on the genuine finite
separated compact core, including arbitrary complex linear combinations. -/
theorem rhoSubharmonicPotential_pi_compact_core_gap {m : ℕ}
    (n : ℕ) (hn : 0 < n) (V : ℂ → ℝ) (ρ : ℝ) (hρpos : 0 < ρ)
    (hV : ContDiff ℝ 2 V) (hρ : IsRhoSubharmonicPotential ρ V)
    (fs : List (ℂ × (Fin (m+1) → PlanarComplexCompactTest))) :
    let F := planarPiCoreWeightedValue n V hV.continuous fs
    ‖F - planarPiBergmanProjection n V hV F‖ ^ 2 ≤
      (2 / ((n : ℝ) * ρ)) *
        ((List.finRange (m+1)).map (fun i => ‖planarPiCoreWeightedDbar n V hV.continuous fs i‖ ^ 2)).sum := by
  obtain ⟨T, hnorm, hT⟩ := rhoSubharmonicPotential_exists_bounded_dbar_inverse n hn V ρ hρpos hV hρ
  let C := 2 / ((n : ℝ) * ρ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hs := Real.sq_sqrt hC
  have hb (i : Fin (m+1)) :
      ‖planarPiCoreWeightedValue n V hV.continuous fs -
        planarPiBergmanCoordinate n V hV i (planarPiCoreWeightedValue n V hV.continuous fs)‖ ^ 2 ≤
      C * ‖planarPiCoreWeightedDbar n V hV.continuous fs i‖ ^ 2 := by
    let S := l2PiCoordinateOperator (fun _ : Fin (m+1) => (volume : Measure ℂ)) i T
    let G := planarPiCoreWeightedDbar n V hV.continuous fs i
    have hb : ‖S‖ ≤ Real.sqrt C := (l2PiCoordinateOperator_norm_le (fun _ : Fin (m+1) => (volume : Measure ℂ)) i T).trans hnorm
    have hh := (S.le_opNorm G).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg G))
    have hsq := (sq_le_sq₀ (norm_nonneg (S G))
      (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg G))).mpr hh
    have he : S G = _ := planarPiCore_inverse_action n V hV T hT fs i
    rw [he] at hsq
    simpa only [mul_pow, hs] using hsq
  have sum_bound (is : List (Fin (m+1))) :
      (is.map (fun i => ‖planarPiCoreWeightedValue n V hV.continuous fs -
        planarPiBergmanCoordinate n V hV i (planarPiCoreWeightedValue n V hV.continuous fs)‖ ^ 2)).sum ≤
      C * (is.map (fun i => ‖planarPiCoreWeightedDbar n V hV.continuous fs i‖ ^ 2)).sum := by
    induction is with
    | nil => simp
    | cons i is ih => simpa only [List.map_cons, List.sum_cons, mul_add] using add_le_add (hb i) ih
  exact (planarPiBergmanProjection_error n V hV _).trans (sum_bound _)

end
end GinibrePoincare
