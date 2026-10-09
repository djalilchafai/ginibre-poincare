module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralIsometry

@[expose] public section

/-! Exact Itô isometry on arbitrary finite, disjoint, possibly empty Brownian intervals. -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem brownianDisjointIntervalSum_isometry {Ω ι κ : Type*}
    [MeasurableSpace Ω] [Fintype ι] [Fintype κ] [DecidableEq κ]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (s d : κ → ℝ≥0)
    (hdisj : ∀ i k, i ≠ k → d i ≠ 0 → d k ≠ 0 → s i+d i ≤ s k ∨ s k+d k ≤ s i)
    (F : κ → Ω → ℝ)
    (hF : ∀ i, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB (s i)) _ (F i))
    (hFi : ∀ i, MemLp (F i) 2 P) :
    (∫ ω, (∑ i, F i ω*(B j (s i+d i) ω-B j (s i) ω))^2 ∂P) =
      ∑ i, (d i : ℝ)*(∫ ω, (F i ω)^2 ∂P) := by
  let X := fun i ω => F i ω*(B j (s i+d i) ω-B j (s i) ω)
  have hX (i : κ) : MemLp (X i) 2 P :=
    ginibreBrownian_augmented_linear_memLp_two B P hB hind (s i) (d i) j (F i) (hF i) (hFi i)
  have hcross (i k : κ) (hne : i ≠ k) : (∫ ω, X i ω*X k ω ∂P) = 0 := by
    by_cases hi : d i = 0
    · simp [X, hi]
    by_cases hk : d k = 0
    · simp [X, hk]
    rcases hdisj i k hne hi hk with hik | hki
    · exact ginibreBrownian_augmented_linear_disjoint_orthogonal B P hB hind
        (s i) (d i) (s k) (d k) hik j j (F i) (F k) (hF i) (hF k)
    · simpa only [X, mul_comm] using ginibreBrownian_augmented_linear_disjoint_orthogonal B P hB hind
        (s k) (d k) (s i) (d i) hki j j (F k) (F i) (hF k) (hF i)
  change (∫ ω, (∑ i, X i ω)^2 ∂P) = _
  rw [ginibre_integral_square_sum_of_cross_zero P X hX hcross]
  apply Finset.sum_congr rfl
  intro i hi
  exact ginibreBrownian_augmented_linear_secondMoment B P hB hind (s i) (d i) j (F i) (hF i)

/-- A common oscillation bound controls the actual disjoint-interval sum. -/
theorem brownianDisjointIntervalSum_secondMoment_le {Ω ι κ : Type*}
    [MeasurableSpace Ω] [Fintype ι] [Fintype κ] [DecidableEq κ]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (s d : κ → ℝ≥0)
    (hdisj : ∀ i k, i ≠ k → d i ≠ 0 → d k ≠ 0 → s i+d i ≤ s k ∨ s k+d k ≤ s i)
    (F : κ → Ω → ℝ)
    (hF : ∀ i, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB (s i)) _ (F i))
    (hFi : ∀ i, MemLp (F i) 2 P) (D : Ω → ℝ)
    (hD : Integrable (fun ω => (D ω)^2) P)
    (hbound : ∀ i ω, ‖F i ω‖ ≤ D ω) :
    (∫ ω, (∑ i, F i ω*(B j (s i+d i) ω-B j (s i) ω))^2 ∂P) ≤
      (∑ i, (d i : ℝ))*(∫ ω, (D ω)^2 ∂P) := by
  rw [brownianDisjointIntervalSum_isometry B P hB hind j s d hdisj F hF hFi]
  calc
    _ ≤ ∑ i, (d i : ℝ)*(∫ ω, (D ω)^2 ∂P) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (d i).coe_nonneg
      apply integral_mono (hFi i).integrable_sq hD
      intro ω
      simpa only [Real.norm_eq_abs, sq_abs] using
        pow_le_pow_left₀ (norm_nonneg _) (hbound i ω) 2
    _ = _ := (Finset.sum_mul _ _ _).symm

end
end GinibrePoincare
