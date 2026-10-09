module

public import GinibrePoincare.Analysis.BrownianIntegralGirsanovTerminalFresh
public import GinibrePoincare.Analysis.BrownianIntegralGaussianFiniteLaw

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def brownianGirsanovCorrectedPrefix {Ω ι : Type*}
    (B : ι → ℝ≥0 → Ω → ℝ) (h : ℕ → Ω → ι → ℝ)
    (τ : ℕ → ℝ≥0) (i : ι) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range n, (B i (τ (k+1)) ω-B i (τ k) ω-
    h k ω i*((τ (k+1)-τ k : ℝ≥0) : ℝ))

theorem brownianGirsanovCorrectedPrefix_measurable_at
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (h : ℕ → Ω → ι → ℝ) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hh : ∀ k, @Measurable Ω (ι→ℝ)
      (ginibreBrownianAugmentedFiltration B P hB (τ k)) _ (h k)) (i : ι) (n : ℕ) :
    @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB (τ n)) _
      (brownianGirsanovCorrectedPrefix B h τ i n) := by
  have hm (k : ℕ) (hk : k ∈ Finset.range n) : @Measurable Ω ℝ
      (ginibreBrownianAugmentedFiltration B P hB (τ n)) _ (fun ω =>
        B i (τ (k+1)) ω-B i (τ k) ω-h k ω i*((τ (k+1)-τ k : ℝ≥0) : ℝ)) := by
    have hk' := Finset.mem_range.mp hk
    exact ((ginibreBrownian_augmented_coordinate_measurable_at B P hB (τ n) _
      (hτ (Nat.succ_le_of_lt hk')) i).sub
      (ginibreBrownian_augmented_coordinate_measurable_at B P hB (τ n) _ (hτ hk'.le) i)).sub
      (((measurable_pi_apply i).comp ((hh k).mono
        ((ginibreBrownianAugmentedFiltration B P hB).mono (hτ hk'.le)) le_rfl)).mul_const _)
  letI : MeasurableSpace Ω := ginibreBrownianAugmentedFiltration B P hB (τ n)
  exact Finset.measurable_sum _ hm

/-- Literal cumulative drift-corrected Brownian coordinate increments have
Gaussian law under the full terminal predictable vector density. -/
theorem brownianGirsanovCorrectedPrefix_gaussian
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (h : ℕ → Ω → ι → ℝ) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hh : ∀ k, @Measurable Ω (ι→ℝ)
      (ginibreBrownianAugmentedFiltration B P hB (τ k)) _ (h k))
    (i : ι) (N n : ℕ) (hn : n ≤ N) :
    HasLaw (brownianGirsanovCorrectedPrefix B h τ i n)
      (gaussianReal 0 (∑ k ∈ Finset.range n, (τ (k+1)-τ k)))
      (P.withDensity (fun ω => ENNReal.ofReal (brownianPredictableVectorGaussianDensity B h τ N ω))) := by
  classical
  let Q := P.withDensity (fun ω => ENNReal.ofReal (brownianPredictableVectorGaussianDensity B h τ N ω))
  letI : IsProbabilityMeasure Q := brownianPredictableVectorGaussianDensity_isProbabilityMeasure B P hB hind h τ hτ hh N
  have hmeas (n : ℕ) : @Measurable Ω ℝ
      (ginibreBrownianAugmentedFiltration B P hB (τ n)) _
      (brownianGirsanovCorrectedPrefix B h τ i n) := by
    have hm (k : ℕ) (hk : k ∈ Finset.range n) : @Measurable Ω ℝ
        (ginibreBrownianAugmentedFiltration B P hB (τ n)) _ (fun ω =>
          B i (τ (k+1)) ω-B i (τ k) ω-h k ω i*((τ (k+1)-τ k : ℝ≥0) : ℝ)) := by
      have hk' := Finset.mem_range.mp hk
      exact ((ginibreBrownian_augmented_coordinate_measurable_at B P hB (τ n) _
        (hτ (Nat.succ_le_of_lt hk')) i).sub
        (ginibreBrownian_augmented_coordinate_measurable_at B P hB (τ n) _ (hτ hk'.le) i)).sub
        (((measurable_pi_apply i).comp ((hh k).mono
          ((ginibreBrownianAugmentedFiltration B P hB).mono (hτ hk'.le)) le_rfl)).mul_const _)
    letI : MeasurableSpace Ω := ginibreBrownianAugmentedFiltration B P hB (τ n)
    exact Finset.measurable_sum _ hm
  induction n with
  | zero =>
    change HasLaw (fun _ => 0) (gaussianReal 0 0) Q
    refine ⟨measurable_const.aemeasurable, ?_⟩
    simp [Measure.map_const, gaussianReal_zero_var]
  | succ n ih =>
    have hnN : n<N := Nat.lt_of_succ_le hn
    have hg := brownianPredictableVectorGaussianDensity_terminal_fresh_increment B P hB hind h τ hτ hh
      n N hnN (brownianGirsanovCorrectedPrefix B h τ i n) (hmeas n)
    dsimp only at hg
    have heval : HasLaw (Function.eval i) (gaussianReal 0 (τ (n+1)-τ n))
        (Measure.pi (fun _ : ι => gaussianReal 0 (τ (n+1)-τ n))) :=
      ⟨(measurable_pi_apply i).aemeasurable, (measurePreserving_eval (fun _ : ι => gaussianReal 0 (τ (n+1)-τ n)) i).map_eq⟩
    have hl := heval.comp hg.1
    have hi := hg.2.comp measurable_id (measurable_pi_apply i)
    have hadd := IndepFun.hasLaw_add (ih (Nat.le_of_succ_le hn)) hl hi
    have heq : brownianGirsanovCorrectedPrefix B h τ i (n+1) =
      brownianGirsanovCorrectedPrefix B h τ i n +
        (fun ω => B i (τ (n+1)) ω-B i (τ n) ω-h n ω i*((τ (n+1)-τ n : ℝ≥0) : ℝ)) := by
      funext ω
      simp only [brownianGirsanovCorrectedPrefix, Finset.sum_range_succ, Pi.add_apply]
    rw [heq, Finset.sum_range_succ]
    change HasLaw (brownianGirsanovCorrectedPrefix B h τ i n +
      (fun ω => B i (τ (n+1)) ω-B i (τ n) ω-h n ω i*((τ (n+1)-τ n : ℝ≥0) : ℝ)))
      (gaussianReal 0 (∑ k ∈ Finset.range n, (τ (k+1)-τ k)) ∗ gaussianReal 0 (τ (n+1)-τ n)) _ at hadd
    simpa only [gaussianReal_conv_gaussianReal, zero_add] using hadd

/-- Literal telescoping identity for the cumulative corrected path. -/
theorem brownianGirsanovCorrectedPrefix_eq {Ω ι : Type*}
    (B : ι → ℝ≥0 → Ω → ℝ) (h : ℕ → Ω → ι → ℝ)
    (τ : ℕ → ℝ≥0) (i : ι) (n : ℕ) (ω : Ω) :
    brownianGirsanovCorrectedPrefix B h τ i n ω = B i (τ n) ω-B i (τ 0) ω-
      ∑ k ∈ Finset.range n, h k ω i*((τ (k+1)-τ k : ℝ≥0) : ℝ) := by
  unfold brownianGirsanovCorrectedPrefix
  simp_rw [Finset.sum_sub_distrib]
  rw [← Finset.sum_sub_distrib, Finset.sum_range_sub (fun k => B i (τ k) ω) n]

end
end GinibrePoincare
