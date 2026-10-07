module

public import GinibrePoincare.Analysis.GinibreStochasticBrownianLinearOrthogonality
public import GinibrePoincare.Analysis.GinibreStochasticBrownianPredictableLinear
public import GinibrePoincare.Analysis.GinibreStochasticOrthogonalSquareSum

@[expose] public section

/-! Actual bounded predictable quadratic-variation errors on ordered intervals. -/
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem ginibreBrownian_predictable_linear_sum_isometry {Ω : Type*}
    [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : IsBrownianReal B P) (n : ℕ) (s t : Fin n → ℝ≥0)
    (hchron : ∀ i j, i < j → s i+t i ≤ s j)
    (F : (i : Fin n) → (Set.Iic (s i) → ℝ) → ℝ)
    (hF : ∀ i, Measurable (F i)) (C : ℝ) (hbound : ∀ i p, ‖F i p‖ ≤ C) :
    (∫ ω, (∑ i, F i (fun v => B v ω)*
      (B (s i+t i) ω-B (s i) ω))^2 ∂P) =
      ∑ i, (t i : ℝ)*(∫ ω, (F i (fun v => B v ω))^2 ∂P) := by
  let X := fun i ω => F i (fun v => B v ω)*
    (B (s i+t i) ω-B (s i) ω)
  have hX (i : Fin n) : MemLp (X i) 2 P :=
    ginibreBrownian_predictable_linear_memLp_two B P hB (s i) (t i) (F i) (hF i) C (hbound i)
  have hcross (i j : Fin n) (hne : i ≠ j) : (∫ ω, X i ω*X j ω ∂P) = 0 := by
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact ginibreBrownian_predictable_linear_cross_zero B P hB
        (s i) (t i) (s j) (t j) (hchron i j hij) (F i) (F j) (hF i) (hF j)
    · simpa only [X, mul_comm] using ginibreBrownian_predictable_linear_cross_zero B P hB
        (s j) (t j) (s i) (t i) (hchron j i hji) (F j) (F i) (hF j) (hF i)
  change (∫ ω, (∑ i, X i ω)^2 ∂P) = _
  rw [ginibre_integral_square_sum_of_cross_zero P X hX hcross]
  apply Finset.sum_congr rfl
  intro i hi
  exact ginibreBrownian_predictable_linear_secondMoment B P hB (s i) (t i) (F i) (hF i)

end
end GinibrePoincare
