module

public import GinibrePoincare.Analysis.GinibreStochasticTransitionL2Sampling
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The actual normalized Bochner Laplace transform of the original stochastic
transition, on the genuine Ginibre L² space. -/
def ginibreOriginalStochasticL2Resolvent {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (c : ℝ)
    (u : Lp ℝ 2 (ginibreMeasure n)) : Lp ℝ 2 (ginibreMeasure n) :=
  ∫ t in Ioi (0:ℝ), (c * Real.exp (-c*t)) •
    ginibreOriginalStochasticL2Operator hn α P B hB hiB t.toNNReal u

theorem ginibreOriginalStochasticL2Resolvent_integrable {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) {c : ℝ} (hc : 0<c)
    (u : Lp ℝ 2 (ginibreMeasure n)) :
    IntegrableOn (fun t : ℝ => (c * Real.exp (-c*t)) •
      ginibreOriginalStochasticL2Operator hn α P B hB hiB t.toNNReal u) (Ioi 0) := by
  have hs : Continuous (fun t : ℝ => (c * Real.exp (-c*t)) •
      ginibreOriginalStochasticL2Operator hn α P B hB hiB t.toNNReal u) :=
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).smul
      ((ginibreOriginalStochasticL2Operator_strong_continuous hn α P B hB hiB u).comp
        continuous_real_toNNReal)
  have hi := (integrableOn_exp_mul_Ioi (show -c<0 by linarith) 0).const_mul (c*‖u‖)
  apply hi.mono' hs.aestronglyMeasurable
  filter_upwards [] with t
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc.le (Real.exp_pos _).le)]
  calc
    c * Real.exp (-c*t) * ‖ginibreOriginalStochasticL2Operator hn α P B hB hiB t.toNNReal u‖
      ≤ c * Real.exp (-c*t) * ‖u‖ := mul_le_mul_of_nonneg_left
        (ginibreOriginalStochasticL2Operator_norm_le hn α P B hB hiB t.toNNReal u)
        (mul_nonneg hc.le (Real.exp_pos _).le)
    _ = c*‖u‖ * Real.exp (-c*t) := by ring

theorem ginibreOriginalStochasticL2Resolvent_pairing {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) {c : ℝ} (hc : 0<c)
    (f u : Lp ℝ 2 (ginibreMeasure n)) :
    inner ℝ f (ginibreOriginalStochasticL2Resolvent hn α P B hB hiB c u) =
      ∫ t in Ioi (0:ℝ), (c*Real.exp (-c*t)) *
        inner ℝ f (ginibreOriginalStochasticL2Operator hn α P B hB hiB t.toNNReal u) := by
  rw [ginibreOriginalStochasticL2Resolvent,
    ← integral_inner (ginibreOriginalStochasticL2Resolvent_integrable hn α P B hB hiB hc u) f]
  simp only [inner_smul_right, RCLike.conj_to_real]

theorem ginibreOriginalStochasticL2Resolvent_symmetric {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (α : ℝ≥0) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) {c : ℝ} (hc : 0<c)
    (f u : Lp ℝ 2 (ginibreMeasure n)) :
    inner ℝ f (ginibreOriginalStochasticL2Resolvent hn α P B hB hiB c u) =
      inner ℝ u (ginibreOriginalStochasticL2Resolvent hn α P B hB hiB c f) := by
  rw [ginibreOriginalStochasticL2Resolvent_pairing hn α P B hB hiB hc,
    ginibreOriginalStochasticL2Resolvent_pairing hn α P B hB hiB hc]
  apply integral_congr_ae
  exact ae_of_all _ fun t => congrArg (fun x => (c*Real.exp (-c*t))*x)
    (ginibreOriginalStochasticL2Operator_symmetric hn α P B hB hiB t.toNNReal f u)

#print axioms ginibreOriginalStochasticL2Resolvent_integrable
end
end GinibrePoincare
