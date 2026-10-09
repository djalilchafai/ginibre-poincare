module

public import GinibrePoincare.Analysis.GinibreDynamicsDrift
public import GinibrePoincare.Analysis.CenterOfMassEigenfunctions
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-! # Pathwise splitting of the additive-noise equation

`IsGinibreDrivenPath` records integrability of the concrete Langevin drift
and its Volterra equation with cumulative noise `N`. The maps
`coordinateSumCLM` and `recenteredCLM` commute with interval integration.
Applying them to the equation and using the drift identities produces the
center OU equation and the autonomous recentered equation.

These results are deterministic: they apply to any driven solution on
nonnegative times. Brownian projection and independence enter later through
`GinibreBrownianProjection`; global path versions and stochastic
factorization are assembled in `BrownianOrthogonalGlobalPathFactorization`
and `BrownianOrthogonalIndependentInitial`. -/

open MeasureTheory
open scoped Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 400000

/-- The actual recentering projection as a continuous real-linear map. -/
def recenteredCLM (n : ℕ) : Configuration n →L[ℝ] Configuration n :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj i -
    ((n : ℝ)⁻¹ • coordinateSumCLM n)

@[simp] theorem recenteredCLM_apply (n : ℕ) (z : Configuration n) :
    recenteredCLM n z = recenteredConfiguration n z := by
  ext i
  simp [recenteredCLM, recenteredConfiguration, projectToOrthogonal,
    Complex.real_smul, div_eq_mul_inv, mul_comm]

/-- The additive-noise Ginibre integral equation with the actual arbitrary-speed drift.
The input `N` is the cumulative driving noise in configuration coordinates. -/
def IsGinibreDrivenPath (n : ℕ) (α : ℝ) (N X : ℝ → Configuration n) : Prop :=
  (∀ t : ℝ, 0 ≤ t → IntervalIntegrable (fun s => ginibreLangevinDrift n α (X s)) volume 0 t) ∧
    ∀ t : ℝ, 0 ≤ t → X t = X 0 + N t + ∫ s in (0 : ℝ)..t, ginibreLangevinDrift n α (X s)

/-- Every actual additive-noise solution satisfies the autonomous center OU
integral equation driven by the summed noise. -/
theorem ginibreDrivenPath_center_equation (n : ℕ) (α : ℝ)
    (N X : ℝ → Configuration n) (hX : IsGinibreDrivenPath n α N X)
    (t : ℝ) (ht : 0 ≤ t) :
    coordinateSum (X t) = coordinateSum (X 0) + coordinateSum (N t) +
      ∫ s in (0 : ℝ)..t, -(2 * α / (n : ℝ)) • coordinateSum (X s) := by
  have he := congrArg (coordinateSumCLM n) (hX.2 t ht)
  simp only [map_add] at he
  rw [← (coordinateSumCLM n).intervalIntegral_comp_comm (hX.1 t ht)] at he
  simpa only [coordinateSumCLM_apply, coordinateSum_ginibreLangevinDrift] using he

/-- Every actual additive-noise solution satisfies the autonomous recentered
integral equation driven by the projected noise. -/
theorem ginibreDrivenPath_recentered_equation (n : ℕ) (α : ℝ)
    (N X : ℝ → Configuration n) (hX : IsGinibreDrivenPath n α N X)
    (t : ℝ) (ht : 0 ≤ t) :
    recenteredConfiguration n (X t) = recenteredConfiguration n (X 0) +
      recenteredConfiguration n (N t) +
      ∫ s in (0 : ℝ)..t, ginibreLangevinDrift n α (recenteredConfiguration n (X s)) := by
  have he := congrArg (recenteredCLM n) (hX.2 t ht)
  simp only [map_add] at he
  rw [← (recenteredCLM n).intervalIntegral_comp_comm (hX.1 t ht)] at he
  simpa only [recenteredCLM_apply, recentered_ginibreLangevinDrift] using he

end
end GinibrePoincare
