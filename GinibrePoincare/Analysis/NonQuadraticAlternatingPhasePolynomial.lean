module

public import GinibrePoincare.Analysis.NonQuadraticHomogeneousPolynomial
public import GinibrePoincare.Analysis.GlobalPhaseAction

@[expose] public section

/-! # Potential-independent bottom alternating phase identification -/
open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem entire_alternating_phase_polynomial {n d : ℕ}
    (F : Configuration n → ℂ) (hF : Differentiable ℂ F) (hA : AnalyticAt ℂ F 0)
    (hAlt : IsAlternating F)
    (hp : ∀ (u : ℂ) (z : Configuration n), ‖u‖ = 1 → F (u • z) = u ^ d * F z) :
    ∃ P : ConfigurationPolynomial n, P.IsHomogeneous d ∧
      IsAlternatingConfigurationPolynomial P ∧ ∀ z, F z = MvPolynomial.eval z P := by
  obtain ⟨P, hP, he⟩ := entire_phase_has_homogeneous_mvPolynomial F hF hA hp
  refine ⟨P, hP, ?_, he⟩
  intro σ
  apply MvPolynomial.funext
  intro z
  rw [eval_permuteConfigurationPolynomial, ← he, map_mul, MvPolynomial.eval_C, ← he]
  exact hAlt σ z

/-- Every nonzero entire alternating phase eigenfunction has degree at
least the Vandermonde degree, for every potential. -/
theorem entire_alternating_phase_degree_lower_bound {n d : ℕ}
    (F : Configuration n → ℂ) (hF : Differentiable ℂ F) (hA : AnalyticAt ℂ F 0)
    (hAlt : IsAlternating F) (hne : F ≠ 0)
    (hp : ∀ (u : ℂ) (z : Configuration n), ‖u‖ = 1 → F (u • z) = u ^ d * F z) :
    vandermondeDegree n ≤ d := by
  obtain ⟨P, hP, hPA, he⟩ := entire_alternating_phase_polynomial F hF hA hAlt hp
  apply vandermondeDegree_le_of_homogeneous_alternating hP hPA
  intro hz
  apply hne
  funext z
  rw [he, hz, map_zero]
  rfl

/-- The bottom entire alternating phase is exactly the Vandermonde line,
without any Gaussian Hilbert-space restriction. -/
theorem entire_alternating_bottom_phase_is_vandermonde {n : ℕ}
    (F : Configuration n → ℂ) (hF : Differentiable ℂ F) (hA : AnalyticAt ℂ F 0)
    (hAlt : IsAlternating F)
    (hp : ∀ (u : ℂ) (z : Configuration n), ‖u‖ = 1 →
      F (u • z) = u ^ vandermondeDegree n * F z) :
    ∃ c : ℂ, ∀ z, F z = c * vandermonde z := by
  obtain ⟨P, hP, hPA, he⟩ := entire_alternating_phase_polynomial F hF hA hAlt hp
  by_cases hz : P = 0
  · refine ⟨0, fun z => ?_⟩
    rw [he, hz, map_zero, zero_mul]
  · obtain ⟨Q, hQ, hfactor⟩ := alternating_polynomial_vandermonde_division hPA
    have hc := quotient_eq_C_of_bottom_homogeneous_degree hP hz hfactor
    refine ⟨Q.coeff 0, fun z => ?_⟩
    rw [he, hfactor, hc, map_mul, MvPolynomial.eval_C, eval_polynomialVandermonde]
    simpa using mul_comm (vandermonde z) (Q.coeff 0)
end
end GinibrePoincare
