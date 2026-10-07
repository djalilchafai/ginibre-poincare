module

public import GinibrePoincare.Analysis.FiniteDimensionalItoLocalTaylor
public import GinibrePoincare.Analysis.FiniteDimensionalItoPartitionRemainder

@[expose] public section

open Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Genuine local C² partition errors vanish on compact subsets of an open domain. -/
theorem itoTaylorRemainder_local_partition_tendsto [ProperSpace E]
    (f : E → ℝ) (U K : Set E) (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (s : ℕ → Finset ℕ) (x y : ℕ → ℕ → E)
    (hx : ∀ k, ∀ i ∈ s k, x k i ∈ K)
    (mesh : ℕ → ℝ) (hm : Tendsto mesh atTop (𝓝 0))
    (hi : ∀ k, ∀ i ∈ s k, ‖y k i - x k i‖ ≤ mesh k)
    (C : ℝ) (hC : 0 ≤ C)
    (hq : ∀ k, ∑ i ∈ s k, ‖y k i - x k i‖^2 ≤ C) :
    Tendsto (fun k => ∑ i ∈ s k, itoTaylorRemainder f (x k i) (y k i - x k i))
      atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : 0 < ε / (C+1) := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hd⟩ := itoTaylorRemainder_uniform_compact_open f U K hU hf hK hKU
    (ε / (C+1)) he
  filter_upwards [hm.eventually (gt_mem_nhds hδ)] with k hk
  rw [dist_zero_right]
  calc
    ‖∑ i ∈ s k, itoTaylorRemainder f (x k i) (y k i-x k i)‖ ≤
        ∑ i ∈ s k, ‖itoTaylorRemainder f (x k i) (y k i-x k i)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s k, (ε / (C+1)) * ‖y k i-x k i‖^2 :=
      Finset.sum_le_sum (fun i his => hd _ (hx k i his) _
        ((hi k i his).trans_lt hk))
    _ = (ε / (C+1)) * ∑ i ∈ s k, ‖y k i-x k i‖^2 := (Finset.mul_sum _ _ _).symm
    _ ≤ (ε / (C+1)) * C := mul_le_mul_of_nonneg_left (hq k) he.le
    _ < ε := by
      have h := mul_lt_mul_of_pos_left (show C < C+1 by linarith) he
      simpa only [div_mul_cancel₀ _ (show C+1 ≠ 0 by linarith)] using h

end
end GinibrePoincare
