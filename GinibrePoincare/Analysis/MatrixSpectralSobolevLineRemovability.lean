module

public import GinibrePoincare.Analysis.MatrixSpectralSobolevSlices
public import GinibrePoincare.Analysis.MatrixSpectralSobolevFTC
public import Mathlib.Analysis.Calculus.Deriv.Comp

@[expose] public section

/-! # Actual weak derivatives across polynomial spectral collisions

A nonzero complex polynomial has only finitely many crossings on almost every
transverse affine coordinate line, by the imported slicing theorem. Along such
a line, the observable is continuous and differentiable outside that finite set.
The finite-exception fundamental theorem then integrates its locally integrable
derivative across the crossings. Compact support of the scalar test removes
the endpoint terms and gives the ordinary weak identity on the line.
-/
open MeasureTheory Filter MvPolynomial
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Continuous functions differentiable away from a genuine nonzero polynomial
zero set satisfy the ordinary weak derivative identity on almost every affine
real coordinate slice as soon as their actual derivatives are locally integrable.
No Sobolev membership or analytic identity is assumed. -/
theorem polynomial_collision_line_weak_identity_ae (d : ℕ)
    (p : MvPolynomial (Fin (d + 1)) ℂ) (hp : p ≠ 0)
    (F : (Fin (d + 1) → ℂ) → ℝ) (hF : Continuous F)
    (hd : ∀ z, MvPolynomial.eval z p ≠ 0 → DifferentiableAt ℝ F z) :
    ∀ᵐ y ∂Measure.pi (fun _ : Fin d => (volume : Measure ℂ)),
      ∀ c v : ℂ, v ≠ 0 →
      LocallyIntegrable (deriv (fun t : ℝ => F (Fin.cons (c + (t : ℂ) * v) y))) volume →
      ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ∀ a b : ℝ, a ≤ b →
        tsupport ψ ⊆ Set.Ioo a b →
        (∫ t : ℝ, deriv (fun s : ℝ => F (Fin.cons (c + (s : ℂ) * v) y)) t * ψ t) =
          -(∫ t : ℝ, F (Fin.cons (c + (t : ℂ) * v) y) * deriv ψ t) := by
  classical
  filter_upwards [complexMvPolynomial_real_line_crossings_finite_ae d p hp] with y hy
  intro c v hv hloc ψ hψ a b hab hsupp
  let f : ℝ → ℝ := fun t => F (Fin.cons (c + (t : ℂ) * v) y)
  let S : Finset ℝ := (hy c v hv).toFinset
  have hc : Continuous f := hF.comp (by fun_prop)
  apply weak_derivative_test_identity_off_finite S f (deriv f) ψ hc hloc _ hψ a b hab hsupp
  intro t ht
  have hpz : MvPolynomial.eval (Fin.cons (c + (t : ℂ) * v) y) p ≠ 0 := by
    simpa only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using ht
  have he : DifferentiableAt ℝ (fun s : ℝ => (s : ℂ)) t :=
    Complex.ofRealCLM.differentiableAt
  exact ((hd _ hpz).comp t (by fun_prop)).hasDerivAt

end
end GinibrePoincare
