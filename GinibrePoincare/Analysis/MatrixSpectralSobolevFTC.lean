module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

@[expose] public section

/-! # Fundamental theorem across finitely many exceptional spectral points -/
open MeasureTheory Set
namespace GinibrePoincare
noncomputable section

/-- A continuous function with integrable derivative off finitely many points
satisfies the genuine fundamental theorem of calculus across those points. -/
theorem integral_derivative_eq_sub_off_finite (S : Finset ℝ) (f g : ℝ → ℝ) :
    ∀ a b : ℝ, a ≤ b → ContinuousOn f (Icc a b) →
      (∀ x ∈ Ioo a b, x ∉ S → HasDerivAt f (g x) x) →
      IntervalIntegrable g volume a b → (∫ x in a..b, g x) = f b - f a := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro a b hab hcont hd hi
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont
      (fun x hx => hd x hx (by simp)) hi
  | @insert c S hc ih =>
    intro a b hab hcont hd hi
    by_cases hmid : c ∈ Ioo a b
    · have hca := hmid.1.le
      have hcb := hmid.2.le
      have hleft : Icc a c ⊆ Icc a b := fun x hx => ⟨hx.1, hx.2.trans hcb⟩
      have hright : Icc c b ⊆ Icc a b := fun x hx => ⟨hca.trans hx.1, hx.2⟩
      have hil : IntervalIntegrable g volume a c := hi.mono_set (by
        simpa only [uIcc_of_le hca, uIcc_of_le hab] using hleft)
      have hir : IntervalIntegrable g volume c b := hi.mono_set (by
        simpa only [uIcc_of_le hcb, uIcc_of_le hab] using hright)
      have hl := ih a c hca (hcont.mono hleft) (by
        intro x hx hxs
        apply hd x ⟨hx.1, hx.2.trans hmid.2⟩
        simp only [Finset.mem_insert, not_or]
        exact ⟨hx.2.ne, hxs⟩) hil
      have hr := ih c b hcb (hcont.mono hright) (by
        intro x hx hxs
        apply hd x ⟨hmid.1.trans hx.1, hx.2⟩
        simp only [Finset.mem_insert, not_or]
        exact ⟨hx.1.ne', hxs⟩) hir
      rw [← intervalIntegral.integral_add_adjacent_intervals hil hir, hl, hr]
      ring
    · apply ih a b hab hcont _ hi
      intro x hx hxs
      apply hd x hx
      simp only [Finset.mem_insert, not_or]
      refine ⟨?_, hxs⟩
      intro hxc
      subst x
      exact hmid hx

/-- Genuine integration by parts remains valid across finitely many singular
points when the observable is continuous and its derivative is integrable. -/
theorem integral_mul_derivative_eq_off_finite (S : Finset ℝ)
    (f g ψ ψ' : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hψ : ContinuousOn ψ (Icc a b))
    (hd : ∀ x ∈ Ioo a b, x ∉ S → HasDerivAt f (g x) x)
    (hψd : ∀ x ∈ Ioo a b, HasDerivAt ψ (ψ' x) x)
    (hgi : IntervalIntegrable (fun x => g x * ψ x) volume a b)
    (hfi : IntervalIntegrable (fun x => f x * ψ' x) volume a b) :
    (∫ x in a..b, g x * ψ x) = f b * ψ b - f a * ψ a -
      (∫ x in a..b, f x * ψ' x) := by
  have he := integral_derivative_eq_sub_off_finite S (fun x => f x * ψ x)
    (fun x => g x * ψ x + f x * ψ' x) a b hab (hf.mul hψ)
    (fun x hx hxs => (hd x hx hxs).mul (hψd x hx)) (hgi.add hfi)
  rw [intervalIntegral.integral_add hgi hfi] at he
  linarith

/-- An actual continuous observable with a locally integrable derivative off
finitely many points satisfies the ordinary weak derivative test identity. -/
theorem weak_derivative_test_identity_off_finite (S : Finset ℝ) (f g ψ : ℝ → ℝ)
    (hf : Continuous f) (hg : LocallyIntegrable g volume)
    (hd : ∀ x, x ∉ S → HasDerivAt f (g x) x)
    (hψ : ContDiff ℝ 1 ψ) (a b : ℝ) (hab : a ≤ b)
    (hsupp : tsupport ψ ⊆ Set.Ioo a b) :
    (∫ x, g x * ψ x) = -(∫ x, f x * deriv ψ x) := by
  have hga : IntervalIntegrable (fun x => g x * ψ x) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    exact (hg.mul_continuous hψ.continuous).integrableOn_isCompact isCompact_Icc
  have hfa : IntervalIntegrable (fun x => f x * deriv ψ x) volume a b :=
    (hf.mul (hψ.continuous_deriv le_rfl)).intervalIntegrable a b
  have ha : ψ a = 0 := by
    by_contra h
    exact (hsupp (subset_closure (show a ∈ Function.support ψ from h))).1.false
  have hb : ψ b = 0 := by
    by_contra h
    exact (hsupp (subset_closure (show b ∈ Function.support ψ from h))).2.false
  have he := integral_mul_derivative_eq_off_finite S f g ψ (deriv ψ) a b hab
    hf.continuousOn hψ.continuous.continuousOn
    (fun x _ hx => hd x hx)
    (fun x _ => (hψ.differentiable one_ne_zero x).hasDerivAt) hga hfa
  rw [intervalIntegral.integral_eq_integral_of_support_subset
    (show Function.support (fun x => g x * ψ x) ⊆ Set.Ioc a b from fun x hx =>
      let h := hsupp (subset_closure ((Function.support_mul_subset_right g ψ) hx));
      ⟨h.1, h.2.le⟩),
    intervalIntegral.integral_eq_integral_of_support_subset
    (show Function.support (fun x => f x * deriv ψ x) ⊆ Set.Ioc a b from fun x hx =>
      let h := hsupp (support_deriv_subset ((Function.support_mul_subset_right f (deriv ψ)) hx));
      ⟨h.1, h.2.le⟩), ha, hb] at he
  simpa using he

end
end GinibrePoincare
