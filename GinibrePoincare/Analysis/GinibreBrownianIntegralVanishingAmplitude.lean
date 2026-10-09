module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralPuncturedContinuous

@[expose] public section

/-! A continuous amplitude vanishing initially removes an integrand's
possible discontinuity at the initial time. -/
open Set Filter
open scoped Topology NNReal
namespace GinibrePoincare

theorem continuous_mul_punctured_of_initial_zero (a f : ℝ≥0 → ℝ)
    (ha : Continuous a) (hf : ContinuousOn f (Ioi 0))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ t, ‖f t‖ ≤ C) (hz : a 0=0) :
    Continuous (fun t => a t*f t) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : t=0
  · subst t
    have hlim : Tendsto (fun t : ℝ≥0 => ‖a t‖*C) (𝓝 0) (𝓝 0) := by
      simpa only [ContinuousAt, hz, norm_zero, zero_mul] using (ha.norm.continuousAt (x := 0)).mul_const C
    have hnorm : Tendsto (fun t : ℝ≥0 => ‖a t*f t‖) (𝓝 0) (𝓝 0) :=
      squeeze_zero (fun t => norm_nonneg _) (fun t => by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hb t) (norm_nonneg _)) hlim
    simpa only [ContinuousAt, hz, zero_mul] using tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  · have hpos : 0 < t := lt_of_le_of_ne bot_le (Ne.symm ht)
    exact ha.continuousAt.mul (hf.continuousAt (isOpen_Ioi.mem_nhds hpos))

#print axioms continuous_mul_punctured_of_initial_zero
end GinibrePoincare
