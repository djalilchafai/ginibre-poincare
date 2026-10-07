module

public import GinibrePoincare.Analysis.BrownianIntegralGaussianConcatenatedGrid

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

theorem brownianUniformLeftSum_concatenated_difference_tendsto_meanSquare
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F t))
    (hFi : ∀ t, MemLp (F t) 2 P) (s t : ℝ≥0)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun r => F r ω) (Set.Icc 0 (s+t)))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ r ω, ‖F r ω‖ ≤ C) :
    Tendsto (fun n => ∫ ω,
      (brownianUniformLeftSum (B j) F (s+t) (n+1) ω-
        brownianActualLeftGridSum (B j) F (itoConcatenatedGrid s t (n+1))
          ((n+1)+(n+1)) ω)^2 ∂P) atTop (𝓝 0) := by
  have hm : Tendsto (fun n : ℕ => ((s+t : ℝ≥0) : ℝ)/(n+1)) atTop (𝓝 0) := by
    have h0 := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa only [mul_zero,mul_one_div] using h0.const_mul ((s+t : ℝ≥0) : ℝ)
  exact brownianActualLeftGridSum_difference_tendsto_meanSquare B P hB hind j F hF hFi
    (s+t) (fun n => itoUniformNNTime (s+t) (n+1))
    (fun n => itoConcatenatedGrid s t (n+1)) (fun n => n+1) (fun n => (n+1)+(n+1))
    (fun n => by omega) (fun n => by omega)
    (fun n => itoUniformNNTime_mono _ _) (fun n => itoConcatenatedGrid_monotone _ _ _ (by omega))
    (fun n => by simp [itoUniformNNTime,itoUniformTime])
    (fun n => itoConcatenatedGrid_zero _ _ _)
    (fun n => itoUniformNNTime_end _ _ (by omega))
    (fun n => itoConcatenatedGrid_end _ _ _ (by omega))
    _ _ hm hm (fun n => by positivity) (fun n => by positivity)
    (fun n k hk => by simpa only [Nat.cast_add,Nat.cast_one] using (itoUniformNNTime_increment_coe (s+t) (n+1) k).le)
    (fun n k hk => by simpa only [Nat.cast_add,Nat.cast_one] using itoConcatenatedGrid_step s t (n+1) k (Nat.succ_pos n)) hcont C hC hbound

end
end GinibrePoincare
