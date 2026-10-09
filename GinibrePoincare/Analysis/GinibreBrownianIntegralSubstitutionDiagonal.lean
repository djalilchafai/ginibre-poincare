module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralSubstitutionRefinement

@[expose] public section

open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- Choose actual inner approximations so the outer mean-square error vanishes. -/
theorem actualMeanSquare_diagonal_selection {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (S : ℕ → ℕ → Ω → ℝ) (I : ℕ → Ω → ℝ)
    (hlim : ∀ n, Tendsto (fun m => ∫ ω, (S n m ω-I n ω)^2 ∂P) atTop (𝓝 0)) :
    ∃ m : ℕ → ℕ, Tendsto (fun n => ∫ ω, (S n (m n) ω-I n ω)^2 ∂P) atTop (𝓝 0) := by
  have hex (n : ℕ) : ∃ m, (∫ ω, (S n m ω-I n ω)^2 ∂P) ≤ 1/((n : ℝ)+1) := by
    have hp : (0 : ℝ)<1/((n : ℝ)+1) := by positivity
    have h := (hlim n).eventually (gt_mem_nhds hp)
    obtain ⟨m, hm⟩ := h.exists
    exact ⟨m, hm.le⟩
  choose m hm using hex
  refine ⟨m,?_⟩
  exact squeeze_zero (fun n => integral_nonneg fun ω => sq_nonneg _) hm
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

end
end GinibrePoincare
