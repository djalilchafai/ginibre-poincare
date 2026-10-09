module

public import GinibrePoincare.Analysis.BrownianIntegralGaussianGridComparison
public import GinibrePoincare.Analysis.GinibreBrownianIntegralFrozenStep

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem brownianActualLeftGridSum_memLp_two
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F t))
    (hFi : ∀ t, MemLp (F t) 2 P) (a : ℕ → ℝ≥0) (ha : Monotone a) (N : ℕ) :
    MemLp (brownianActualLeftGridSum (B j) F a N) 2 P := by
  apply memLp_finsetSum
  intro k hk
  have hh := brownianFrozenStep_memLp_two B P hB hind j (F (a k)) (a k)
    (a (k+1)) (a (k+1)) (hF _) (hFi _)
  have he : brownianFrozenStep (B j) (F (a k)) (a k) (a (k+1)) (a (k+1)) =
      (fun ω => F (a k) ω*(B j (a (k+1)) ω-B j (a k) ω)) := by
    funext ω
    simp [brownianFrozenStep, max_eq_right (ha (Nat.le_succ k))]
  rw [he] at hh
  exact hh

end
end GinibrePoincare
