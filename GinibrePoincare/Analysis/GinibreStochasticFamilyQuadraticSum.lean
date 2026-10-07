module

public import GinibrePoincare.Analysis.GinibreStochasticAugmentedWeightedHessian
public import GinibrePoincare.Analysis.GinibreStochasticProbabilityOperations

@[expose] public section

/-! Actual finite Brownian-family scalar quadratic sums converge in probability. -/
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000

def ginibreBrownianFamilyQuadraticSum {Ω ι : Type*} [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i, ∑ l : Fin (n+1),
    (B i (ginibreUniformBrownianTime T n (l.val+1)) ω-
      B i (ginibreUniformBrownianTime T n l) ω)^2

theorem ginibreBrownianFamilyQuadraticSum_tendstoInProbability {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (T : ℝ≥0) :
    TendstoInMeasure P (ginibreBrownianFamilyQuadraticSum B T) atTop
      (fun _ => (Fintype.card ι : ℝ)*(T : ℝ)) := by
  classical
  let A : ι → ι → ℝ≥0 → Ω → ℝ := fun i j _ _ => if i=j then 1 else 0
  have h := ginibreBrownianAugmentedWeightedHessian_tendstoInProbability B P hB hind T A
    (fun i j t => stronglyMeasurable_const)
    (fun i j => Filter.Eventually.of_forall (fun ω => continuous_const))
    1 (by intro i j s ω; simp [A]; split_ifs <;> norm_num)
  convert! h using 1
  · funext n ω
    simp only [ginibreBrownianFamilyQuadraticSum, ginibreBrownianAugmentedWeightedHessian,
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i hi
    simp [A, pow_two]
  · funext ω
    simp [A]
end
end GinibrePoincare
