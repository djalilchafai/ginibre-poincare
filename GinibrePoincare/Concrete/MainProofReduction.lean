module

public import GinibrePoincare.Concrete.AnalyticStatements
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Checked endgame of the main proof

After normalizing the ground-state transform, the proof has the scalar shape

* `E = 4 D`;
* `δ_γ ≤ D`;
* `δ_γ = δ_μ`;
* `Var / 2 ≤ δ_μ`.

The first theorem verifies this scalar implication.  The second applies it to
the literal Ginibre quantities.  Its five hypotheses are displayed separately;
there is no bundled certificate argument.
-/

namespace GinibrePoincare

/-- Exact scalar implication used in the main proof. -/
theorem mainProof_scalar_endgame
    (variance energy dbarEnergy gaussianDistance ginibreDistance : ℝ)
    (hEnergy : energy = 4 * dbarEnergy)
    (hGaussian : gaussianDistance ≤ dbarEnergy)
    (hIsometry : gaussianDistance = ginibreDistance)
    (hHalf : variance / 2 ≤ ginibreDistance) :
    variance ≤ energy / 2 := by
  linarith

/-- The smooth-core theorem follows from the five concrete analytic statements. -/
theorem smoothGinibrePoincare_of_main_analytic_statements
    (hAdmissible : GroundStateAdmissibilityStatement)
    (hEnergy : GroundStateEnergyIdentityStatement)
    (hGaussian : GaussianDbarEstimateStatement)
    (hDistance : GroundStateDistanceIdentityStatement)
    (hHalf : GinibreHalfDistanceStatement) :
    SmoothGinibrePoincareStatement := by
  intro n hn hProbability f hf
  let g : Configuration n → ℂ :=
    normalizedVandermondeTransform n
      (fun z => (centeredObservable n f z : ℂ))
  have hgAdmissible : IsGaussianDbarAdmissible n g := by
    exact hAdmissible n hn hProbability f hf
  have hgEnergy :
      smoothGinibreEnergy n f = 4 * gaussianDbarEnergy n g := by
    exact hEnergy n hn hProbability f hf
  have hgGaussian :
      gaussianHolomorphicDistanceSq n g ≤ gaussianDbarEnergy n g := by
    exact hGaussian n hn g hgAdmissible
  have hgDistance :
      gaussianHolomorphicDistanceSq n g =
        ginibreHolomorphicDistanceSq n (centeredObservable n f) := by
    exact hDistance n hn hProbability f hf
  have hgHalf :
      smoothGinibreVariance n f / 2 ≤
        ginibreHolomorphicDistanceSq n (centeredObservable n f) := by
    exact hHalf n hn hProbability f hf
  exact mainProof_scalar_endgame
    (smoothGinibreVariance n f)
    (smoothGinibreEnergy n f)
    (gaussianDbarEnergy n g)
    (gaussianHolomorphicDistanceSq n g)
    (ginibreHolomorphicDistanceSq n (centeredObservable n f))
    hgEnergy hgGaussian hgDistance hgHalf

end GinibrePoincare
