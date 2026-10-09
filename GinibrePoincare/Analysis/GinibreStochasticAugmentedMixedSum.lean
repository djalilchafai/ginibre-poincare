module

public import GinibrePoincare.Analysis.GinibreStochasticAugmentedMixedOrthogonality
public import GinibrePoincare.Analysis.GinibreStochasticOrthogonalSquareSum

@[expose] public section

/-! Actual augmented predictable finite quadratic-error sum bounds. -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem ginibreBrownian_augmented_mixed_sum_secondMoment_le {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j l : ι) (hjl : j ≠ l) (n : ℕ) (s t : Fin n → ℝ≥0)
    (hchron : ∀ i k, i < k → s i+t i ≤ s k) (F : Fin n → Ω → ℝ)
    (hF : ∀ i, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB (s i)) _ (F i))
    (C : ℝ) (hbound : ∀ i ω, ‖F i ω‖ ≤ C) :
    (∫ ω, (∑ i, F i ω*((B j (s i+t i) ω-B j (s i) ω)*(B l (s i+t i) ω-B l (s i) ω)))^2 ∂P) ≤
      C^2*∑ i, (t i : ℝ)^2 := by
  let X := fun i ω => F i ω*((B j (s i+t i) ω-B j (s i) ω)*(B l (s i+t i) ω-B l (s i) ω))
  have hFM (i : Fin n) : Measurable (F i) := (hF i).mono ((ginibreBrownianAugmentedFiltration B P hB).le _) le_rfl
  have hFi (i : Fin n) : MemLp (F i) 2 P := MemLp.of_bound (hFM i).aestronglyMeasurable C (Eventually.of_forall (hbound i))
  have hX (i : Fin n) : MemLp (X i) 2 P :=
    ginibreBrownian_augmented_mixed_memLp_two B P hB hind (s i) (t i) j l hjl (F i) (hF i) (hFi i)
  have hcross (i k : Fin n) (hne : i ≠ k) : (∫ ω, X i ω*X k ω ∂P) = 0 := by
    rcases lt_or_gt_of_ne hne with hik | hki
    · exact ginibreBrownian_augmented_mixed_disjoint_orthogonal B P hB hind
        (s i) (t i) (s k) (t k) (hchron i k hik) j l j l hjl (F i) (F k) (hF i) (hF k)
    · rw [show (∫ ω, X i ω*X k ω ∂P) = (∫ ω, X k ω*X i ω ∂P) from
        integral_congr_ae (Eventually.of_forall (fun ω => mul_comm _ _))]
      exact ginibreBrownian_augmented_mixed_disjoint_orthogonal B P hB hind
        (s k) (t k) (s i) (t i) (hchron k i hki) j l j l hjl (F k) (F i) (hF k) (hF i)
  change (∫ ω, (∑ i, X i ω)^2 ∂P) ≤ _
  rw [ginibre_integral_square_sum_of_cross_zero P X hX hcross]
  calc
    _ ≤ ∑ i, C^2*(t i : ℝ)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      rw [ginibreBrownian_augmented_mixed_secondMoment B P hB hind (s i) (t i) j l hjl (F i) (hF i)]
      have hI : (∫ ω, (F i ω)^2 ∂P) ≤ C^2 := by
        have h := integral_mono_ae (hFi i).integrable_sq (integrable_const (C^2))
          (Eventually.of_forall (fun ω => show (F i ω)^2 ≤ C^2 from by
            have hh := pow_le_pow_left₀ (norm_nonneg (F i ω)) (hbound i ω) 2
            simpa only [Real.norm_eq_abs, sq_abs] using hh))
        simpa using h
      nlinarith [mul_le_mul_of_nonneg_left hI (show 0 ≤ (t i : ℝ)^2 by positivity)]
    _ = _ := by rw [Finset.mul_sum]

end
end GinibrePoincare
