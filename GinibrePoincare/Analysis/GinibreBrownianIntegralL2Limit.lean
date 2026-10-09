module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralMeanSquareCauchy
public import GinibrePoincare.Analysis.EntropyL2Closure
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

@[expose] public section

/-! A genuine L² limit of the actual predictable Brownian left sums. -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem brownianUniformLeftSum_memLp_two {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F t))
    (hFi : ∀ t, MemLp (F t) 2 P) (T : ℝ≥0) (N : ℕ) :
    MemLp (brownianUniformLeftSum (B j) F T N) 2 P := by
  unfold brownianUniformLeftSum
  apply memLp_finsetSum
  intro i hi
  let s := itoUniformNNTime T N i
  let d := itoUniformNNTime T N (i+1)-s
  have hend : s+d = itoUniformNNTime T N (i+1) :=
    add_tsub_cancel_of_le (itoUniformNNTime_mono T N (Nat.le_succ i))
  have h := ginibreBrownian_augmented_linear_memLp_two B P hB hind s d j (F s) (hF s) (hFi s)
  simpa only [hend, s] using h

theorem brownianUniformLeftSum_cauchySeq_L2 {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F t))
    (hFi : ∀ t, MemLp (F t) 2 P) (T : ℝ≥0)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => F t ω) (Set.Icc 0 T))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ t ∈ Set.Icc 0 T, ∀ ω, ‖F t ω‖ ≤ C) :
    CauchySeq (fun n => (brownianUniformLeftSum_memLp_two B P hB hind j F hF hFi T (n+1)).toLp
      (brownianUniformLeftSum (B j) F T (n+1))) := by
  let S := fun n => brownianUniformLeftSum (B j) F T (n+1)
  let hs := fun n => brownianUniformLeftSum_memLp_two B P hB hind j F hF hFi T (n+1)
  let Z := fun n => (hs n).toLp (S n)
  have he (q : ℕ×ℕ) : dist (Z q.1) (Z q.2) = Real.sqrt (∫ ω, (S q.1 ω-S q.2 ω)^2 ∂P) := by
    have hh : (∫ ω, (S q.1 ω-S q.2 ω)^2 ∂P) = ‖Z q.1-Z q.2‖^2 := by
      rw [← integral_square_eq_L2_norm_sq]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (Z q.1) (Z q.2), (hs q.1).coeFn_toLp, (hs q.2).coeFn_toLp]
        with ω hω h1 h2
      simp only [hω, Pi.sub_apply]
      dsimp only [Z, S]
      rw [h1, h2]
    rw [hh, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), dist_eq_norm]
  change CauchySeq Z
  apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
  have ht := (brownianUniformLeftSum_tendsto_difference_meanSquare B P hB hind j F hF hFi T hc C hC hbound).sqrt
  change Tendsto (fun q : ℕ×ℕ => Real.sqrt (∫ ω, (S q.1 ω-S q.2 ω)^2 ∂P)) atTop (𝓝 (Real.sqrt 0)) at ht
  simpa only [he, Real.sqrt_zero] using ht

theorem brownianUniformLeftSum_exists_L2_limit {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F t))
    (hFi : ∀ t, MemLp (F t) 2 P) (T : ℝ≥0)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => F t ω) (Set.Icc 0 T))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ t ∈ Set.Icc 0 T, ∀ ω, ‖F t ω‖ ≤ C) :
    ∃ I : Lp ℝ 2 P, Tendsto (fun n =>
      (brownianUniformLeftSum_memLp_two B P hB hind j F hF hFi T (n+1)).toLp
        (brownianUniformLeftSum (B j) F T (n+1))) atTop (𝓝 I) :=
  cauchySeq_tendsto_of_complete (brownianUniformLeftSum_cauchySeq_L2 B P hB hind j F hF hFi T hc C hC hbound)

end
end GinibrePoincare
