module

public import GinibrePoincare.Analysis.GinibreStochasticOUPath
public import GinibrePoincare.Analysis.GinibreOUTransition

@[expose] public section

/-! # A concrete Brownian time-change realization of the OU kernels

Exponential time change gives continuous sample paths with the exact Gaussian
OU transition marginal from a deterministic starting point.
-/

open MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- Exponential Brownian clock for OU equilibrium variance one half. -/
def ginibreOUBrownianClock (rate t : ℝ≥0) : ℝ≥0 :=
  Real.toNNReal ((Real.exp (2 * (rate : ℝ) * (t : ℝ)) - 1) / 2)

 theorem ginibreOUBrownianClock_coe (rate t : ℝ≥0) :
    (ginibreOUBrownianClock rate t : ℝ) =
      (Real.exp (2 * (rate : ℝ) * (t : ℝ)) - 1) / 2 := by
  apply Real.coe_toNNReal
  have he : 1 ≤ Real.exp (2 * (rate : ℝ) * (t : ℝ)) :=
    Real.one_le_exp_iff.mpr (by positivity)
  positivity

 theorem ginibreOUBrownianClock_variance (rate t : ℝ≥0) :
    (NNReal.mk (ginibreOUDecay rate t ^ 2) (sq_nonneg _)) * ginibreOUBrownianClock rate t =
      ginibreOUVariance rate t := by
  apply NNReal.eq
  rw [NNReal.coe_mul, ginibreOUBrownianClock_coe, ginibreOUVariance_coe]
  change ginibreOUDecay rate t ^ 2 *
    ((Real.exp (2 * (rate : ℝ) * (t : ℝ)) - 1) / 2) = _
  have he : ginibreOUDecay rate t ^ 2 * Real.exp (2 * (rate : ℝ) * (t : ℝ)) = 1 := by
    simp only [ginibreOUDecay, pow_two]
    rw [← Real.exp_add, ← Real.exp_add]
    ring_nf
    simp
  nlinarith

/-- A real OU process constructed directly from an actual Brownian process. -/
def ginibreTimeChangedOU {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (rate : ℝ≥0) (x : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ginibreOUDecay rate t * (x + B (ginibreOUBrownianClock rate t) ω)

 theorem ginibreTimeChangedOU_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (rate : ℝ≥0) (x : ℝ) (t : ℝ≥0) :
    HasLaw (ginibreTimeChangedOU B rate x t) (ginibreOUTransition rate t x) P := by
  have h := gaussianReal_const_mul
    (gaussianReal_const_add (hB.hasLaw_eval (ginibreOUBrownianClock rate t)) x)
    (ginibreOUDecay rate t)
  change HasLaw (fun ω => ginibreOUDecay rate t *
    (x + B (ginibreOUBrownianClock rate t) ω))
    (gaussianReal (ginibreOUDecay rate t * x) (ginibreOUVariance rate t)) P
  simpa only [zero_add, ginibreOUBrownianClock_variance] using h

 theorem ginibreTimeChangedOU_continuous {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P)
    (rate : ℝ≥0) (x : ℝ) :
    ∀ᵐ ω ∂P, Continuous (fun t => ginibreTimeChangedOU B rate x t ω) := by
  filter_upwards [hB.cont] with ω hω
  have hclock : Continuous (ginibreOUBrownianClock rate) := by
    unfold ginibreOUBrownianClock
    fun_prop
  have hdecay : Continuous (ginibreOUDecay rate) := by
    unfold ginibreOUDecay
    fun_prop
  exact hdecay.mul (continuous_const.add (hω.comp hclock))

end
end GinibrePoincare
