module

public import GinibrePoincare.Analysis.MatrixSpectralSobolevLineRemovability
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

/-! # Removal of collisions for the actual directional derivative representative -/
open MeasureTheory Filter MvPolynomial
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem polynomial_collision_candidate_line_weak_identity_ae (d : ℕ)
    (p : MvPolynomial (Fin (d + 1)) ℂ) (hp : p ≠ 0)
    (F : (Fin (d + 1) → ℂ) → ℝ) (hF : Continuous F)
    (hd : ∀ z, MvPolynomial.eval z p ≠ 0 → DifferentiableAt ℝ F z) :
    ∀ᵐ y ∂Measure.pi (fun _ : Fin d => (volume : Measure ℂ)),
      ∀ c v : ℂ, v ≠ 0 →
      let g := fun t : ℝ => fderiv ℝ F (Fin.cons (c + (t : ℂ) * v) y)
        (Fin.cons v 0)
      LocallyIntegrable g volume →
      ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ∀ a b : ℝ, a ≤ b →
        tsupport ψ ⊆ Set.Ioo a b →
        (∫ t : ℝ, g t * ψ t) =
          -(∫ t : ℝ, F (Fin.cons (c + (t : ℂ) * v) y) * deriv ψ t) := by
  classical
  filter_upwards [complexMvPolynomial_real_line_crossings_finite_ae d p hp] with y hy
  intro c v hv
  dsimp only
  intro hg ψ hψ a b hab hsupp
  let f : ℝ → ℝ := fun t => F (Fin.cons (c + (t : ℂ) * v) y)
  let S : Finset ℝ := (hy c v hv).toFinset
  apply weak_derivative_test_identity_off_finite S f _ ψ
    (hF.comp (by fun_prop)) hg _ hψ a b hab hsupp
  intro t ht
  have hpz : MvPolynomial.eval (Fin.cons (c + (t : ℂ) * v) y) p ≠ 0 := by
    simpa only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using ht
  have hl : HasDerivAt
      (fun s : ℝ => (Fin.cons (c + (s : ℂ) * v) y : Fin (d + 1) → ℂ))
      (Fin.cons v 0) t := by
    apply hasDerivAt_pi.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change HasDerivAt (fun s : ℝ => c + (s : ℂ) * v) v t
      convert (hasDerivAt_const t c).add
        ((Complex.ofRealCLM.hasFDerivAt.hasDerivAt).mul_const v) using 1 <;> first | rfl | simp only [zero_add, Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul]
    · simpa using hasDerivAt_const t (y j)
  exact (hd _ hpz).hasFDerivAt.comp_hasDerivAt t hl

end
end GinibrePoincare
