module

public import GinibrePoincare.Analysis.GinibreStochasticOUFunctional
public import GinibrePoincare.Analysis.GinibreDrivenPathOUShift

@[expose] public section

/-! # Independent innovations of the actual driven OU solution -/
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

/-- The actual OU response to the fresh Brownian increments after time `s`. -/
def ginibreBrownianOUInnovation {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (rate s t : ℝ≥0) : Ω → ℝ :=
  ginibreBrownianOU (fun u ω => B (s + u) ω - B s ω) rate (Real.sqrt (rate : ℝ)) 0 t

 theorem ginibreBrownianOU_step_ae {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P)
    (rate s t : ℝ≥0) (x : ℝ) :
    ∀ᵐ ω ∂P, ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) x (s + t) ω =
      ginibreOUDecay rate t * ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) x s ω +
        ginibreBrownianOUInnovation B rate s t ω := by
  filter_upwards [hB.cont] with ω hcont
  let N := ginibreBrownianNoise B (Real.sqrt (rate : ℝ)) ω
  have hN : Continuous N := continuous_const.mul (hcont.comp continuous_real_toNNReal)
  have h := drivenOUPath_shift (rate : ℝ) x N hN (s : ℝ) (t : ℝ)
  have hM : drivenOUPath rate (drivenOUPath rate x N s) (fun u => N ((s : ℝ) + u) - N s) t =
      drivenOUPath rate (drivenOUPath rate x N s)
        (ginibreBrownianNoise (fun u ω => B (s + u) ω - B s ω)
          (Real.sqrt (rate : ℝ)) ω) t := by
    apply drivenOUPath_congr_nonneg _ _ _ _ _ t.coe_nonneg
    intro u hu
    simp only [N, ginibreBrownianNoise, Real.toNNReal_add s.coe_nonneg hu.1,
      Real.toNNReal_coe, mul_sub]
  rw [hM] at h
  conv_rhs at h => rw [drivenOUPath_initial_split]
  simpa only [ginibreBrownianOU, ginibreBrownianOUInnovation, ginibreOUDecay,
    NNReal.coe_add, N, smul_eq_mul] using h

 theorem ginibreBrownianOUInnovation_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P)
    (rate s t : ℝ≥0) :
    HasLaw (ginibreBrownianOUInnovation B rate s t)
      (gaussianReal 0 (ginibreOUVariance rate t)) P := by
  have h := ginibreBrownianOU_zero_hasLaw _ P (hB.shift s) rate t
  have hk : ginibreOUTransition rate t 0 = gaussianReal 0 (ginibreOUVariance rate t) := by
    change gaussianReal (ginibreOUDecay rate t * 0) (ginibreOUVariance rate t) = _
    rw [mul_zero]
  rw [hk] at h
  exact h

 theorem ginibreBrownianOUInnovation_independent_past {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P)
    (rate s t : ℝ≥0) :
    IndepFun (ginibreBrownianOUInnovation B rate s t)
      (fun ω (v : Set.Iic s) => B v ω) P :=
  ginibreBrownianOU_shift_independent_past B P hB rate s t

end
end GinibrePoincare
