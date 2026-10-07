module

public import GinibrePoincare.Analysis.MatrixPolynomialNull

@[expose] public section

/-! # Finite discriminant crossings on almost every real coordinate line -/
open MeasureTheory MvPolynomial
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- A nonzero complex polynomial has only finitely many zeros on every
nonconstant affine real line in the complex plane. -/
theorem complexPolynomial_affine_real_zeros_finite (p : Polynomial ℂ) (hp : p ≠ 0)
    (c v : ℂ) (hv : v ≠ 0) :
    {t : ℝ | p.eval (c + (t : ℂ) * v) = 0}.Finite := by
  have hi : Function.Injective (fun t : ℝ => c + (t : ℂ) * v) := by
    intro s t h
    have hst := mul_right_cancel₀ hv (add_left_cancel h)
    exact_mod_cast hst
  exact (Polynomial.finite_setOfPred_isRoot hp).preimage hi.injOn

/-- For an actual nonzero multivariate complex polynomial, almost every
remaining-coordinate configuration admits only finitely many crossings on
EVERY nonconstant real affine line in the distinguished coordinate. -/
theorem complexMvPolynomial_real_line_crossings_finite_ae (d : ℕ)
    (p : MvPolynomial (Fin (d + 1)) ℂ) (hp : p ≠ 0) :
    ∀ᵐ y ∂Measure.pi (fun _ : Fin d => (volume : Measure ℂ)),
      ∀ c v : ℂ, v ≠ 0 →
        {t : ℝ | MvPolynomial.eval (Fin.cons (c + (t : ℂ) * v) y) p = 0}.Finite := by
  let q := MvPolynomial.finSuccEquiv ℂ d p
  have hq : q ≠ 0 := by
    intro h
    exact hp ((MvPolynomial.finSuccEquiv ℂ d).injective (by simpa [q] using h))
  obtain ⟨k, hk⟩ : ∃ k, q.coeff k ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hq (Polynomial.ext fun k => by simpa using h k)
  filter_upwards [complexMvPolynomial_fin_eval_ne_zero_ae volume d (q.coeff k) hk] with y hy
  have hmap : q.map (MvPolynomial.eval y) ≠ 0 := by
    intro hz
    have hc := congrArg (fun f : Polynomial ℂ => f.coeff k) hz
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hc
    exact hy hc
  intro c v hv
  simpa only [MvPolynomial.eval_eq_eval_mv_eval'] using
    complexPolynomial_affine_real_zeros_finite (q.map (MvPolynomial.eval y)) hmap c v hv

end
end GinibrePoincare
