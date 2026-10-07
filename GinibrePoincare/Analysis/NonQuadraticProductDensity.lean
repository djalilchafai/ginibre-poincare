module

public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

/-! # Finite product densities without an integrability assumption
Tonelli's theorem applies to arbitrary measurable nonnegative weights, before
normalization or finiteness of their masses has been established.
-/
open MeasureTheory
open scoped ENNReal BigOperators
namespace GinibrePoincare
noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- The extended nonnegative integral of a separable finite product factors,
including infinite values. -/
theorem lintegral_fin_prod_eq_prod {n : ℕ} {E : Type*} [MeasurableSpace E]
    {μ : Fin n → Measure E} [∀ i, SigmaFinite (μ i)]
    (f : Fin n → E → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x : Fin n → E, ∏ i, f i (x i) ∂Measure.pi μ) =
      ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp [Measure.pi_empty_univ]
  | succ n ih =>
    calc
      _ = ∫⁻ x : E × (Fin n → E),
          f 0 x.1 * ∏ i, f (Fin.succ i) (x.2 i)
          ∂((μ 0).prod (Measure.pi (fun i => μ i.succ))) := by
        have hmp := (measurePreserving_piFinSuccAbove μ 0).symm
        rw [← hmp.lintegral_comp
          (by exact Finset.measurable_prod _ fun i _ => (hf i).comp (measurable_pi_apply i))]
        simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Fin.prod_univ_succ, Fin.insertNth_zero, Fin.zero_succAbove]
        rfl
      _ = (∫⁻ x, f 0 x ∂μ 0) *
          ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂μ i.succ := by
        rw [lintegral_prod_mul (f := f 0) (g := fun x : Fin n → E => ∏ i, f i.succ (x i)) (hf 0).aemeasurable
          (by exact (Finset.measurable_prod _ fun i _ =>
            (hf i.succ).comp (measurable_pi_apply i)).aemeasurable), ih]
        exact fun i => hf i.succ
      _ = _ := by rw [Fin.prod_univ_succ]

set_option backward.isDefEq.respectTransparency false in
/-- Finite products of finite-valued densities preserve product structure,
with no separate coordinate integrability premise. -/
theorem pi_withDensity_ofReal_eq_unconditional {n : ℕ} {E : Type*} [MeasurableSpace E]
    (μ : Fin n → Measure E) [∀ i, SigmaFinite (μ i)]
    (w : Fin n → E → ℝ) (hw : ∀ i, Measurable (w i))
    (hp : ∀ i x, 0 ≤ w i x) :
    Measure.pi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (w i x))) =
      (Measure.pi μ).withDensity (fun x => ENNReal.ofReal (∏ i, w i (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  simp_rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => hp i _)]
  rw [lintegral_fin_prod_eq_prod (fun i x => ENNReal.ofReal (w i x)) (fun i => (hw i).ennreal_ofReal)]
  · congr 1
    funext i
    rw [withDensity_apply _ (hs i)]


#print axioms lintegral_fin_prod_eq_prod
#print axioms pi_withDensity_ofReal_eq_unconditional
end
end GinibrePoincare
