module
public import GinibrePoincare.Analysis.NonQuadraticBochner
@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

/-- The variable Hessian term in the concrete weighted Bochner identity is
controlled by the generator norm. No constant lower curvature bound is used. -/
theorem correspondenceBrascampLieb_scalar_hessian_bound
    (W f : ℝ → ℝ) (hW : ContDiff ℝ 2 W) (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) :
    (∫ x, deriv (deriv W) x * deriv f x ^ 2 * scalarConfinementWeight W x) ≤
      ∫ x, scalarConfinementGenerator W f x ^ 2 * scalarConfinementWeight W x := by
  rw [scalarConfinement_bochner_identity W f hW hf hc]
  exact le_add_of_nonneg_left (integral_nonneg fun x =>
    mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)

#print axioms correspondenceBrascampLieb_scalar_hessian_bound
end
end GinibrePoincare
