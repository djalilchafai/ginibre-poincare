module

public import GinibrePoincare.Analysis.GinibreStochasticCenterSmallStopping

@[expose] public section

/-! Actual center lower bounds before its small-radius stopping time. -/
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreCenterSquared_gt_before_small_hitting {Ω : Type*} {n : ℕ}
    (X : ℝ≥0 → Ω → Configuration n) (C δ : ℝ) (T t : ℝ≥0) (ω : Ω)
    (hb : ∀ t ω, ginibreCenterSquared n (X t ω) ≤ C)
    (ht : t < hittingBtwn (fun s ω => C-ginibreCenterSquared n (X s ω))
      {x : ℝ | C-δ ≤ ‖x‖} 0 T ω) :
    δ < ginibreCenterSquared n (X t ω) := by
  have hh := notMem_of_lt_hittingBtwn ht (bot_le : (0 : ℝ≥0) ≤ t)
  change ¬ C-δ ≤ ‖C-ginibreCenterSquared n (X t ω)‖ at hh
  rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (hb t ω))] at hh
  exact (by linarith [not_le.mp hh])

/-- Continuity includes the stopping endpoint in the actual lower bound. -/
theorem ginibreCenterSquared_ge_until_small_hitting {Ω : Type*} {n : ℕ}
    (X : ℝ≥0 → Ω → Configuration n) (C δ : ℝ) (T t : ℝ≥0) (ω : Ω)
    (hb : ∀ t ω, ginibreCenterSquared n (X t ω) ≤ C)
    (hc : Continuous (fun s => ginibreCenterSquared n (X s ω)))
    (h0 : δ ≤ ginibreCenterSquared n (X 0 ω))
    (ht : t ≤ hittingBtwn (fun s ω => C-ginibreCenterSquared n (X s ω))
      {x : ℝ | C-δ ≤ ‖x‖} 0 T ω) :
    δ ≤ ginibreCenterSquared n (X t ω) := by
  let θ := hittingBtwn (fun s ω => C-ginibreCenterSquared n (X s ω))
      {x : ℝ | C-δ ≤ ‖x‖} 0 T ω
  obtain hlt | heq := lt_or_eq_of_le ht
  · exact (ginibreCenterSquared_gt_before_small_hitting X C δ T t ω hb hlt).le
  · by_cases hθ : θ=0
    · have ht0 : t=0 := heq.trans hθ
      simpa only [ht0] using h0
    · have hθpos : 0 < θ := lt_of_le_of_ne bot_le (Ne.symm hθ)
      let S := {s : ℝ≥0 | δ ≤ ginibreCenterSquared n (X s ω)}
      have hS : IsClosed S := isClosed_le continuous_const hc
      have hsub : Iio θ ⊆ S := fun s hs =>
        (ginibreCenterSquared_gt_before_small_hitting X C δ T s ω hb hs).le
      have hmem : θ ∈ closure (Iio θ) := by
        rw [closure_Iio' (show (Iio θ).Nonempty from ⟨0,hθpos⟩)]
        exact (show θ ≤ θ from le_rfl)
      exact heq ▸ (hS.closure_subset_iff.mpr hsub hmem)

#print axioms ginibreCenterSquared_ge_until_small_hitting
#print axioms ginibreCenterSquared_gt_before_small_hitting
end
end GinibrePoincare
