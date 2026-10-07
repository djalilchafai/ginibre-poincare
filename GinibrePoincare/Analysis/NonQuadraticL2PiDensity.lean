module

public import GinibrePoincare.Analysis.NonQuadraticL2PiProducts

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

theorem l2ProductMaps_ext_on_pure {A B H : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [NormedAddCommGroup H] [NormedSpace ℂ H] {η : Measure A} {ξ : Measure B}
    [SigmaFinite η] [SigmaFinite ξ]
    (S T : Lp ℂ 2 (η.prod ξ) →L[ℂ] H)
    (h : ∀ u v, S (l2ProductVector u v) = T (l2ProductVector u v)) : S = T := by
  apply ContinuousLinearMap.ext
  intro F
  obtain ⟨x, rfl⟩ := l2ProductCompletedTensorEquiv_sigmaFinite.surjective F
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq
      (S.continuous.comp (l2ProductCompletedTensorEquiv_sigmaFinite (μ := η) (ν := ξ)).continuous)
      (T.continuous.comp (l2ProductCompletedTensorEquiv_sigmaFinite (μ := η) (ν := ξ)).continuous)
  | ih x =>
    rw [l2ProductTensorEquiv_coe]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul u v => exact h u v
    | add x y hx hy => simp only [map_add, hx, hy]

 theorem l2PiOperators_ext_on_pure {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [NormedSpace ℂ H] (n : ℕ)
    (μ : Fin n → Measure X) [∀ i, SigmaFinite (μ i)]
    (S T : Lp ℂ 2 (Measure.pi μ) →L[ℂ] H)
    (h : ∀ u : ∀ i, Lp ℂ 2 (μ i), S (l2PiProductVector μ u) = T (l2PiProductVector μ u)) : S = T := by
  induction n with
  | zero =>
    apply ContinuousLinearMap.ext
    intro F
    let p : Fin 0 → X := fun i => Fin.elim0 i
    let u : ∀ i : Fin 0, Lp ℂ 2 (μ i) := fun i => Fin.elim0 i
    have hf : F = F p • l2PiProductVector μ u := by
      apply Lp.ext
      filter_upwards [l2PiProductVector_coeFn μ u,
        Lp.coeFn_smul (F p) (l2PiProductVector μ u)] with z hz hs
      rw [hs]
      change F z = F p * l2PiProductVector μ u z
      rw [hz]
      simp only [Finset.univ_eq_empty, Finset.prod_empty, smul_eq_mul, mul_one]
      congr 1
      exact Subsingleton.elim _ _
    rw [hf, map_smul, map_smul, h]
  | succ m ih =>
    let i : Fin (m+1) := 0
    let ν : Fin m → Measure X := fun j => μ (i.succAbove j)
    let E := l2PiCoordinateEquiv μ i
    have he : S.comp E.symm.toLinearIsometry.toContinuousLinearMap =
        T.comp E.symm.toLinearIsometry.toContinuousLinearMap := by
      apply l2ProductMaps_ext_on_pure
      intro a b
      let L := l2ProductContinuousBilinear (μ := μ i) (ν := Measure.pi ν) a
      have hl : (S.comp E.symm.toLinearIsometry.toContinuousLinearMap).comp L =
          (T.comp E.symm.toLinearIsometry.toContinuousLinearMap).comp L := by
        apply ih ν
        intro v
        let u : ∀ j, Lp ℂ 2 (μ j) := Fin.insertNth i a v
        have hu : E (l2PiProductVector μ u) = l2ProductVector a (l2PiProductVector ν v) := by
          rw [l2PiProductVector_split]
          simp only [u, ν, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
        have hei : E.symm (l2ProductVector a (l2PiProductVector ν v)) = l2PiProductVector μ u := by
          rw [← hu, LinearIsometryEquiv.symm_apply_apply]
        change S (E.symm (l2ProductVector a (l2PiProductVector ν v))) =
          T (E.symm (l2ProductVector a (l2PiProductVector ν v)))
        rw [hei]
        exact h u
      exact DFunLike.congr_fun hl b
    apply ContinuousLinearMap.ext
    intro F
    have hh := DFunLike.congr_fun he (E F)
    change S (E.symm (E F)) = T (E.symm (E F)) at hh
    simpa only [LinearIsometryEquiv.symm_apply_apply] using hh

theorem l2PiCoordinateOperators_commute {X : Type*} [MeasurableSpace X] {m : ℕ}
    (μ : Fin (m+1) → Measure X) [∀ i, SigmaFinite (μ i)]
    (i j : Fin (m+1)) (hij : i ≠ j)
    (A : Lp ℂ 2 (μ i) →L[ℂ] Lp ℂ 2 (μ i))
    (B : Lp ℂ 2 (μ j) →L[ℂ] Lp ℂ 2 (μ j)) :
    (l2PiCoordinateOperator μ i A).comp (l2PiCoordinateOperator μ j B) =
      (l2PiCoordinateOperator μ j B).comp (l2PiCoordinateOperator μ i A) := by
  apply l2PiOperators_ext_on_pure (m+1) μ
  intro u
  simp only [ContinuousLinearMap.comp_apply, l2PiCoordinateOperator_pure]
  congr 1
  funext k
  by_cases hki : k = i
  · subst k
    simp [hij, hij.symm]
  · by_cases hkj : k = j
    · subst k
      simp [hij, hij.symm]
    · simp [hki, hkj]

end
end GinibrePoincare
