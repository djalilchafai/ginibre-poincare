module

public import GinibrePoincare.Analysis.BrownianIntegralGirsanovPrefixLaw

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- The entire actual corrected vector innovation array has the genuine
product Gaussian law under the full terminal predictable likelihood. -/
theorem brownianPredictableVectorGaussianDensity_corrected_product_law
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (h : ℕ → Ω → ι → ℝ) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hh : ∀ k, @Measurable Ω (ι→ℝ)
      (ginibreBrownianAugmentedFiltration B P hB (τ k)) _ (h k)) (N : ℕ) :
    HasLaw (fun ω (k : Fin N) i => B i (τ (k.val+1)) ω-B i (τ k) ω-
      h k ω i*((τ (k.val+1)-τ k : ℝ≥0) : ℝ))
      (Measure.pi (fun k : Fin N => Measure.pi (fun _ : ι => gaussianReal 0 (τ (k.val+1)-τ k))))
      (P.withDensity (fun ω => ENNReal.ofReal (brownianPredictableVectorGaussianDensity B h τ N ω))) := by
  classical
  let Q := P.withDensity (fun ω => ENNReal.ofReal (brownianPredictableVectorGaussianDensity B h τ N ω))
  letI : IsProbabilityMeasure Q := brownianPredictableVectorGaussianDensity_isProbabilityMeasure B P hB hind h τ hτ hh N
  let W := fun k ω i => B i (τ (k+1)) ω-B i (τ k) ω-h k ω i*((τ (k+1)-τ k : ℝ≥0) : ℝ)
  let Z := fun k ω => if k<N then W k ω else (0 : ι→ℝ)
  have hm (k : ℕ) : @Measurable Ω (ι→ℝ)
      (ginibreBrownianAugmentedFiltration B P hB (τ (k+1))) _ (W k) := by
    refine (@measurable_pi_iff Ω ι (fun _ => ℝ)
      (ginibreBrownianAugmentedFiltration B P hB (τ (k+1))) (fun _ => inferInstance) (W k)).mpr ?_
    intro i
    exact ((ginibreBrownian_augmented_coordinate_measurable_at B P hB (τ (k+1)) _ le_rfl i).sub
      (ginibreBrownian_augmented_coordinate_measurable_at B P hB (τ (k+1)) _ (hτ (Nat.le_succ k)) i)).sub
      (((measurable_pi_apply i).comp ((hh k).mono
        ((ginibreBrownianAugmentedFiltration B P hB).mono (hτ (Nat.le_succ k))) le_rfl)).mul_const _)
  have hi : iIndepFun Z Q := by
    apply chronologicalFresh_iIndepFun Q
      (sampledMartingaleFiltration (ginibreBrownianAugmentedFiltration B P hB) τ hτ) Z
    · intro k
      by_cases hk : k<N
      · simpa only [Z,if_pos hk] using hm k
      · simp only [Z,if_neg hk]
        exact measurable_const
    · intro k Y hY
      by_cases hk : k<N
      · have hf := brownianPredictableVectorGaussianDensity_terminal_fresh_increment B P hB hind h τ hτ hh k N hk Y hY
        simpa only [Z,if_pos hk,W,Q] using hf.2
      · simp only [Z,if_neg hk]
        exact indepFun_const_right Y 0
  have hif := hi.precomp (g := fun k : Fin N => k.val) Fin.val_injective
  have heq : (fun k : Fin N => Z k)=(fun k : Fin N => W k) := by
    funext k ω
    simp only [Z,if_pos k.isLt]
  rw [heq] at hif
  apply hif.hasLaw_pi
  intro k
  exact (brownianPredictableVectorGaussianDensity_terminal_fresh_increment B P hB hind h τ hτ hh
    k N k.isLt (fun _ => (0:ℝ)) measurable_const).1

/-- Original vector innovation array on the identical chronological grid has
exactly the same actual product law. -/
theorem brownianFamilyGridInnovation_product_law
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (N : ℕ) :
    HasLaw (fun ω (k : Fin N) i => B i (τ (k.val+1)) ω-B i (τ k) ω)
      (Measure.pi (fun k : Fin N => Measure.pi (fun _ : ι => gaussianReal 0 (τ (k.val+1)-τ k)))) P := by
  have hl := brownianPredictableVectorGaussianDensity_corrected_product_law B P hB hind
    (fun _ _ _ => 0) τ hτ (fun _ => measurable_const) N
  simpa [brownianPredictableVectorGaussianDensity] using hl

/-- Every actual measurable functional of the finite corrected grid has the
same law as its original Brownian grid counterpart. -/
theorem brownianPredictableVectorGaussianDensity_corrected_grid_identDistrib
    {Ω ι E : Type*} [MeasurableSpace Ω] [Fintype ι] [MeasurableSpace E]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (h : ℕ → Ω → ι → ℝ) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hh : ∀ k, @Measurable Ω (ι→ℝ)
      (ginibreBrownianAugmentedFiltration B P hB (τ k)) _ (h k))
    (N : ℕ) (f : (Fin N → ι → ℝ) → E) (hf : Measurable f) :
    IdentDistrib
      (fun ω => f (fun (k : Fin N) i => B i (τ (k.val+1)) ω-B i (τ k) ω-
        h k ω i*((τ (k.val+1)-τ k : ℝ≥0) : ℝ)))
      (fun ω => f (fun (k : Fin N) i => B i (τ (k.val+1)) ω-B i (τ k) ω))
      (P.withDensity (fun ω => ENNReal.ofReal (brownianPredictableVectorGaussianDensity B h τ N ω))) P := by
  have hc := brownianPredictableVectorGaussianDensity_corrected_product_law B P hB hind h τ hτ hh N
  have hb := brownianFamilyGridInnovation_product_law B P hB hind τ hτ N
  exact (hc.identDistrib hb).comp hf

end
end GinibrePoincare
