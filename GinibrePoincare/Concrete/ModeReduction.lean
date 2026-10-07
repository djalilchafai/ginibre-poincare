module

public import GinibrePoincare.Concrete.SmoothTarget
public import GinibrePoincare.Endgame.SeriesDeficit
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Concrete mode-by-mode reduction

This file identifies precisely how an actual sequence of Gaussian mode
functions feeds the already checked infinite-series algebra.  It does not
postulate a Hermite basis: the mode functions and the three analytic identities
remain explicit hypotheses of the theorem.
-/

open MeasureTheory
open scoped BigOperators

namespace GinibrePoincare

noncomputable section

/-- Squared Gaussian `L²` mass of a complex function. -/
def gaussianModeMass (n : ℕ) (g : Configuration n → ℂ) : ℝ :=
  ∫ z, Complex.normSq (g z) ∂complexGaussianMeasure n

/-- Shifted sequence `a_k = ‖g_{k+1}‖²`. -/
def positiveModeMasses (n : ℕ)
    (modes : ℕ → Configuration n → ℂ) (k : ℕ) : ℝ :=
  gaussianModeMass n (modes (k + 1))

/-- Concrete deficit identity from actual mode functions and visible identities. -/
theorem smoothGinibre_deficit_of_mode_identities
    (n : ℕ)
    (f : Configuration n → ℝ)
    (modes : ℕ → Configuration n → ℂ)
    (holomorphicSq remainderSq : ℝ)
    (hSummable : Summable (positiveModeMasses n modes))
    (hTailSummable :
      Summable (fun k : ℕ =>
        (k : ℝ) * positiveModeMasses n modes k))
    (hParseval :
      smoothGinibreVariance n f =
        holomorphicSq + modeMass (positiveModeMasses n modes))
    (hGeometry :
      smoothGinibreVariance n f =
        2 * holomorphicSq + remainderSq)
    (hEnergy :
      smoothGinibreEnergy n f =
        4 * modeEnergy (positiveModeMasses n modes)) :
    smoothGinibreEnergy n f - 2 * smoothGinibreVariance n f =
      2 * remainderSq + 4 * modeTail (positiveModeMasses n modes) := by
  exact infinite_deficit_identity
    (positiveModeMasses n modes)
    hSummable hTailSummable
    (smoothGinibreVariance n f)
    holomorphicSq remainderSq
    (smoothGinibreEnergy n f)
    hParseval hGeometry hEnergy

/-- Poincaré follows when the concrete remainder and all mode masses are nonnegative. -/
theorem smoothGinibre_poincare_of_mode_identities
    (n : ℕ)
    (f : Configuration n → ℝ)
    (modes : ℕ → Configuration n → ℂ)
    (holomorphicSq remainderSq : ℝ)
    (hSummable : Summable (positiveModeMasses n modes))
    (hTailSummable :
      Summable (fun k : ℕ =>
        (k : ℝ) * positiveModeMasses n modes k))
    (hParseval :
      smoothGinibreVariance n f =
        holomorphicSq + modeMass (positiveModeMasses n modes))
    (hGeometry :
      smoothGinibreVariance n f =
        2 * holomorphicSq + remainderSq)
    (hEnergy :
      smoothGinibreEnergy n f =
        4 * modeEnergy (positiveModeMasses n modes))
    (hRemainder : 0 ≤ remainderSq) :
    smoothGinibreVariance n f ≤ smoothGinibreEnergy n f / 2 := by
  apply infinite_poincare_half
    (positiveModeMasses n modes)
    hSummable hTailSummable
    (smoothGinibreVariance n f)
    holomorphicSq remainderSq
    (smoothGinibreEnergy n f)
    hParseval hGeometry hEnergy hRemainder
  intro k
  unfold positiveModeMasses gaussianModeMass
  exact integral_nonneg fun z => Complex.normSq_nonneg _

end

end GinibrePoincare
