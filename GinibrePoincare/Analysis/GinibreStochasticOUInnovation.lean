module

public import GinibrePoincare.Analysis.GinibreStochasticOUTimeChange

@[expose] public section

/-! # Actual independent innovations of the Brownian OU realization -/
open MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem ginibreOUBrownianClock_mono (rate s t : ℝ≥0) :
    ginibreOUBrownianClock rate s ≤ ginibreOUBrownianClock rate (s + t) := by
  apply NNReal.coe_le_coe.mp
  rw [ginibreOUBrownianClock_coe, ginibreOUBrownianClock_coe]
  have h : Real.exp (2 * (rate : ℝ) * (s : ℝ)) ≤
      Real.exp (2 * (rate : ℝ) * ((s + t : ℝ≥0) : ℝ)) := by
    apply Real.exp_le_exp.mpr
    simp only [NNReal.coe_add]
    nlinarith [rate.coe_nonneg, t.coe_nonneg]
  linarith

 theorem ginibreOUBrownianClock_monotone (rate : ℝ≥0) :
    Monotone (ginibreOUBrownianClock rate) := by
  intro a b hab
  have h := ginibreOUBrownianClock_mono rate a (b - a)
  rwa [add_tsub_cancel_of_le hab] at h

 theorem ginibreOUBrownianClock_increment_variance (rate s t : ℝ≥0) :
    NNReal.mk (ginibreOUDecay rate (s + t) ^ 2) (sq_nonneg _) *
      (ginibreOUBrownianClock rate (s + t) - ginibreOUBrownianClock rate s) =
      ginibreOUVariance rate t := by
  apply NNReal.eq
  rw [NNReal.coe_mul, NNReal.coe_sub (ginibreOUBrownianClock_mono rate s t)]
  have hst := congrArg (fun v : ℝ≥0 => (v : ℝ))
    (ginibreOUBrownianClock_variance rate (s + t))
  have hs := congrArg (fun v : ℝ≥0 => (v : ℝ))
    (ginibreOUBrownianClock_variance rate s)
  simp only [NNReal.coe_mul, NNReal.coe_mk] at hst hs ⊢
  rw [ginibreOUVariance_add, ginibreOUDecay_add] at hst
  rw [ginibreOUDecay_add]
  have hs2 := congrArg (fun z : ℝ => ginibreOUDecay rate t ^ 2 * z) hs
  nlinarith

/-- The actual OU innovation, extracted from a disjoint Brownian increment. -/
def ginibreOUInnovation {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (rate s t : ℝ≥0) (ω : Ω) : ℝ :=
  ginibreOUDecay rate (s + t) *
    (B (ginibreOUBrownianClock rate (s + t)) ω - B (ginibreOUBrownianClock rate s) ω)

 theorem ginibreTimeChangedOU_step {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (rate s t : ℝ≥0) (x : ℝ) (ω : Ω) :
    ginibreTimeChangedOU B rate x (s + t) ω =
      ginibreOUDecay rate t * ginibreTimeChangedOU B rate x s ω +
        ginibreOUInnovation B rate s t ω := by
  simp only [ginibreTimeChangedOU, ginibreOUInnovation, ginibreOUDecay_add]
  ring

 theorem ginibreOUInnovation_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (rate s t : ℝ≥0) :
    HasLaw (ginibreOUInnovation B rate s t) (gaussianReal 0 (ginibreOUVariance rate t)) P := by
  have hmono := ginibreOUBrownianClock_mono rate s t
  have h := (hB.shift (ginibreOUBrownianClock rate s)).hasLaw_eval
    (ginibreOUBrownianClock rate (s + t) - ginibreOUBrownianClock rate s)
  have hmul := gaussianReal_const_mul h (ginibreOUDecay rate (s + t))
  change HasLaw (fun ω => ginibreOUDecay rate (s + t) *
    (B (ginibreOUBrownianClock rate (s + t)) ω - B (ginibreOUBrownianClock rate s) ω))
    (gaussianReal 0 (ginibreOUVariance rate t)) P
  simpa only [add_tsub_cancel_of_le hmono, mul_zero,
    ginibreOUBrownianClock_increment_variance] using hmul

 theorem ginibreOUInnovation_independent {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (rate s t : ℝ≥0) (x : ℝ) :
    IndepFun (ginibreOUInnovation B rate s t) (ginibreTimeChangedOU B rate x s) P := by
  let a := ginibreOUBrownianClock rate s
  let d := ginibreOUBrownianClock rate (s + t) - a
  have h := (hB.indepFun_shift a).comp
    (φ := fun f : ℝ≥0 → ℝ => ginibreOUDecay rate (s + t) * f d)
    (ψ := fun f : Set.Iic a → ℝ => ginibreOUDecay rate s * (x + f ⟨a, (Set.mem_Iic.mpr le_rfl)⟩))
    (by fun_prop) (by fun_prop)
  change IndepFun (fun ω => ginibreOUDecay rate (s + t) *
    (B (ginibreOUBrownianClock rate (s + t)) ω - B (ginibreOUBrownianClock rate s) ω))
    (fun ω => ginibreOUDecay rate s * (x + B (ginibreOUBrownianClock rate s) ω)) P
  simpa only [Function.comp_def,
    a, d, add_tsub_cancel_of_le (ginibreOUBrownianClock_mono rate s t)] using h

/-- Each actual innovation is independent of the entire OU history up to the
preceding time, not just of the value at that time. -/
theorem ginibreOUInnovation_independent_past {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (rate s t : ℝ≥0) (x : ℝ) :
    IndepFun (ginibreOUInnovation B rate s t)
      (fun ω (v : Set.Iic s) => ginibreTimeChangedOU B rate x v ω) P := by
  let a := ginibreOUBrownianClock rate s
  let d := ginibreOUBrownianClock rate (s + t) - a
  let past : (Set.Iic a → ℝ) → (Set.Iic s → ℝ) := fun f v =>
    ginibreOUDecay rate v * (x + f ⟨ginibreOUBrownianClock rate v,
      Set.mem_Iic.mpr (ginibreOUBrownianClock_monotone rate v.property)⟩)
  have hpast : Measurable past := by
    apply measurable_pi_lambda
    intro v
    exact measurable_const.mul (measurable_const.add (measurable_pi_apply _))
  have h := (hB.indepFun_shift a).comp
    (φ := fun f : ℝ≥0 → ℝ => ginibreOUDecay rate (s + t) * f d)
    (ψ := past) (by fun_prop) hpast
  change IndepFun (fun ω => ginibreOUDecay rate (s + t) *
    (B (ginibreOUBrownianClock rate (s + t)) ω - B (ginibreOUBrownianClock rate s) ω))
    (fun ω (v : Set.Iic s) => ginibreOUDecay rate v *
      (x + B (ginibreOUBrownianClock rate v) ω)) P
  simpa only [Function.comp_def, past, a, d,
    add_tsub_cancel_of_le (ginibreOUBrownianClock_mono rate s t)] using h

end
end GinibrePoincare
