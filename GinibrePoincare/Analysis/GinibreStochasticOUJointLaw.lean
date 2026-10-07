module

public import GinibrePoincare.Analysis.GinibreStochasticOUPast

@[expose] public section

/-! # Actual two-time OU law for the Brownian-driven integral-equation solution -/
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem ginibreBrownianOU_two_time_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P)
    (rate s t : ℝ≥0) (x : ℝ) :
    HasLaw (fun ω => (ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) x s ω,
      ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) x (s + t) ω))
      (((ginibreOUTransition rate s x).prod (gaussianReal 0 (ginibreOUVariance rate t))).map
        (fun p : ℝ × ℝ => (p.1, ginibreOUDecay rate t * p.1 + p.2))) P := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  let μ := (ginibreOUTransition rate s x).prod (gaussianReal 0 (ginibreOUVariance rate t))
  let F : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, ginibreOUDecay rate t * p.1 + p.2)
  have hp := (ginibreBrownianOUInnovation_independent_value B P hB rate s t x).symm.hasLaw_prod
    (ginibreBrownianOU_hasLaw B P hB rate s x)
    (ginibreBrownianOUInnovation_hasLaw B P hB rate s t)
  have hF : HasLaw F (μ.map F) μ := ⟨by fun_prop, rfl⟩
  have h := hF.comp hp
  apply h.congr
  filter_upwards [ginibreBrownianOU_step_ae B P hB rate s t x] with ω hω
  change (ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) x s ω,
    ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) x (s + t) ω) =
    (ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) x s ω,
      ginibreOUDecay rate t * ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) x s ω +
        ginibreBrownianOUInnovation B rate s t ω)
  rw [hω]

end
end GinibrePoincare
