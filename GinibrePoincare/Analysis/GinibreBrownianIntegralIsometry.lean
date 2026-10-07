module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralLinear

@[expose] public section

/-! Exact discrete Itô isometry for the actual augmented joint Brownian filtration. -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem ginibreBrownian_augmented_linear_sum_isometry {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (n : ℕ) (s t : Fin n → ℝ≥0)
    (hchron : ∀ i k, i < k → s i+t i ≤ s k) (F : Fin n → Ω → ℝ)
    (hF : ∀ i, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB (s i)) _ (F i))
    (hFi : ∀ i, MemLp (F i) 2 P) :
    (∫ ω, (∑ i, F i ω*(B j (s i+t i) ω-B j (s i) ω))^2 ∂P) =
      ∑ i, (t i : ℝ)*(∫ ω, (F i ω)^2 ∂P) := by
  let X := fun i ω => F i ω*(B j (s i+t i) ω-B j (s i) ω)
  have hX (i : Fin n) : MemLp (X i) 2 P :=
    ginibreBrownian_augmented_linear_memLp_two B P hB hind (s i) (t i) j (F i) (hF i) (hFi i)
  have hcross (i k : Fin n) (hne : i ≠ k) : (∫ ω, X i ω*X k ω ∂P) = 0 := by
    rcases lt_or_gt_of_ne hne with hik | hki
    · exact ginibreBrownian_augmented_linear_disjoint_orthogonal B P hB hind
        (s i) (t i) (s k) (t k) (hchron i k hik) j j (F i) (F k) (hF i) (hF k)
    · simpa only [X, mul_comm] using ginibreBrownian_augmented_linear_disjoint_orthogonal B P hB hind
        (s k) (t k) (s i) (t i) (hchron k i hki) j j (F k) (F i) (hF k) (hF i)
  change (∫ ω, (∑ i, X i ω)^2 ∂P) = _
  rw [ginibre_integral_square_sum_of_cross_zero P X hX hcross]
  apply Finset.sum_congr rfl
  intro i hi
  exact ginibreBrownian_augmented_linear_secondMoment B P hB hind (s i) (t i) j (F i) (hF i)

theorem ginibreBrownian_augmented_linear_sum_memLp_two {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (n : ℕ) (s t : Fin n → ℝ≥0) (F : Fin n → Ω → ℝ)
    (hF : ∀ i, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB (s i)) _ (F i))
    (hFi : ∀ i, MemLp (F i) 2 P) :
    MemLp (fun ω => ∑ i, F i ω*(B j (s i+t i) ω-B j (s i) ω)) 2 P := by
  convert! memLp_finsetSum Finset.univ (fun i _ =>
    ginibreBrownian_augmented_linear_memLp_two B P hB hind (s i) (t i) j (F i) (hF i) (hFi i)) using 1

end
end GinibrePoincare
