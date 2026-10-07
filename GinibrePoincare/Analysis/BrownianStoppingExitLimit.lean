module

public import GinibrePoincare.Analysis.BrownianStoppingExitLyapunov

@[expose] public section

/-! Vanishing probability of arbitrarily high Lyapunov exits. -/
open MeasureTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

theorem measure_iInter_eq_zero_of_reciprocal_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (E : ℕ → Set Ω) (C : ℝ)
    (hE : ∀ m, μ.real (E m) ≤ C/((m : ℝ)+1)) : μ (⋂ m, E m) = 0 := by
  have hlim : Tendsto (fun m : ℕ => C/((m : ℝ)+1)) atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      (tendsto_const_nhds (x := C)).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hb : ∀ m : ℕ, μ.real (⋂ k, E k) ≤ C/((m : ℝ)+1) := fun m =>
    (measureReal_mono (Set.iInter_subset E m)).trans (hE m)
  have hz : μ.real (⋂ k, E k) ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hb)
  exact (measureReal_eq_zero_iff).mp (le_antisymm hz (measureReal_nonneg))

end
end GinibrePoincare
