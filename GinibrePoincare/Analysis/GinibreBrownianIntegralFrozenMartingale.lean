module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralFrozenConditional
public import GinibrePoincare.Analysis.GinibreBrownianIntegralL2Limit

@[expose] public section

/-! Actual frozen steps, and their uniform finite sums, are continuous martingales. -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem brownianFrozenStep_martingale {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : Ω → ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (hF : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB a) _ F)
    (hFi : MemLp F 2 P) :
    Martingale (brownianFrozenStep (B j) F a b) (ginibreBrownianAugmentedFiltration B P hB) P := by
  refine ⟨brownianFrozenStep_stronglyAdapted B P hB j F a b hF, ?_⟩
  intro s t hst
  have hs := brownianFrozenStep_conditional_terminal B P hB hind j F a b s hab hF hFi
  have ht := brownianFrozenStep_conditional_terminal B P hB hind j F a b t hab hF hFi
  have htw := condExp_condExp_of_le ((ginibreBrownianAugmentedFiltration B P hB).mono hst)
    ((ginibreBrownianAugmentedFiltration B P hB).le t)
    (f := fun ω => F ω*(B j b ω-B j a ω)) (μ := P)
  exact (condExp_congr_ae ht.symm).trans (htw.trans hs)

def brownianUniformPartialSum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (F : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (N : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range N, brownianFrozenStep B (F (itoUniformNNTime T N i))
    (itoUniformNNTime T N i) (itoUniformNNTime T N (i+1)) t ω

theorem brownianUniformPartialSum_martingale {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F t))
    (hFi : ∀ t, MemLp (F t) 2 P) (T : ℝ≥0) (N : ℕ) :
    Martingale (brownianUniformPartialSum (B j) F T N) (ginibreBrownianAugmentedFiltration B P hB) P := by
  have hm (i : ℕ) := brownianFrozenStep_martingale B P hB hind j (F (itoUniformNNTime T N i))
    (itoUniformNNTime T N i) (itoUniformNNTime T N (i+1))
    (itoUniformNNTime_mono T N (Nat.le_succ i)) (hF _) (hFi _)
  have hsum : Martingale (∑ i ∈ Finset.range N, brownianFrozenStep (B j) (F (itoUniformNNTime T N i))
      (itoUniformNNTime T N i) (itoUniformNNTime T N (i+1))) (ginibreBrownianAugmentedFiltration B P hB) P := by
    have hall (S : Finset ℕ) : Martingale (∑ i ∈ S, brownianFrozenStep (B j) (F (itoUniformNNTime T N i))
        (itoUniformNNTime T N i) (itoUniformNNTime T N (i+1))) (ginibreBrownianAugmentedFiltration B P hB) P := by
      induction S using Finset.induction_on with
      | empty => simpa using martingale_zero ℝ (ginibreBrownianAugmentedFiltration B P hB) P
      | @insert i S hi ih =>
        rw [Finset.sum_insert hi]
        exact (hm i).add ih
    exact hall (Finset.range N)
  have he : brownianUniformPartialSum (B j) F T N =
      ∑ i ∈ Finset.range N, brownianFrozenStep (B j) (F (itoUniformNNTime T N i))
        (itoUniformNNTime T N i) (itoUniformNNTime T N (i+1)) := by
    funext t ω
    simp only [brownianUniformPartialSum, Finset.sum_apply]
  rw [he]
  exact hsum

end
end GinibrePoincare
