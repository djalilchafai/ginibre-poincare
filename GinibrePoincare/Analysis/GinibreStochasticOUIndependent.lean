module

public import GinibrePoincare.Analysis.GinibreStochasticOUJointLaw

@[expose] public section

/-! # Independence of actual OU paths driven by independent Brownian motions -/
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 def ginibreOUValueFunctional (rate t : ℝ≥0) (x : ℝ) (path : ℝ≥0 → ℝ) : ℝ :=
  ginibreOUDecay rate t * x + ginibreOUConvolutionFunctional rate t path

 theorem ginibreOUValueFunctional_measurable (rate t : ℝ≥0) (x : ℝ) :
    Measurable (ginibreOUValueFunctional rate t x) :=
  measurable_const.add (ginibreOUConvolutionFunctional_measurable rate t)

 theorem ginibreOUValueFunctional_ae_eq {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P)
    (rate t : ℝ≥0) (x : ℝ) :
    (fun ω => ginibreOUValueFunctional rate t x (fun s => B s ω)) =ᵐ[P]
      ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) x t := by
  filter_upwards [ginibreOUConvolutionFunctional_ae_eq B P hB rate t] with ω hω
  change ginibreOUDecay rate t * x +
    ginibreOUConvolutionFunctional rate t (fun s => B s ω) = _
  rw [hω]
  change Real.exp (-(rate : ℝ) * (t : ℝ)) * x +
    drivenOUPath rate 0 (ginibreBrownianNoise B (Real.sqrt (rate : ℝ)) ω) t =
      drivenOUPath rate x (ginibreBrownianNoise B (Real.sqrt (rate : ℝ)) ω) t
  conv_rhs => rw [drivenOUPath_initial_split]
  rfl

 theorem ginibreBrownianOU_independent {Ω : Type*} [MeasurableSpace Ω]
    (B C : ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : IsBrownianReal B P) (hC : IsBrownianReal C P)
    (hind : IndepFun (fun ω s => B s ω) (fun ω s => C s ω) P)
    (rateB rateC s t : ℝ≥0) (x y : ℝ) :
    IndepFun (ginibreBrownianOU B rateB (Real.sqrt (rateB : ℝ)) x s)
      (ginibreBrownianOU C rateC (Real.sqrt (rateC : ℝ)) y t) P := by
  have h := hind.comp (ginibreOUValueFunctional_measurable rateB s x)
    (ginibreOUValueFunctional_measurable rateC t y)
  exact h.congr (ginibreOUValueFunctional_ae_eq B P hB rateB s x)
    (ginibreOUValueFunctional_ae_eq C P hC rateC t y)

end
end GinibrePoincare
