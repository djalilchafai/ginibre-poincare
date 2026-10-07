module

public import GinibrePoincare.Analysis.GinibreStochasticAugmentedQuadraticOrthogonality
public import GinibrePoincare.Analysis.GinibreStochasticOrthogonalSquareSum

@[expose] public section

/-! Linear Brownian innovations with coefficients measurable in the genuine augmented past. -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem ginibreBrownian_augmented_linear_secondMoment {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (s t : ℝ≥0) (i : ι) (F : Ω → ℝ)
    (hF : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB s) _ F) :
    (∫ ω, (F ω*(B i (s+t) ω-B i s ω))^2 ∂P) =
      (t : ℝ)*(∫ ω, (F ω)^2 ∂P) := by
  have hZ : HasLaw (fun ω => B i (s+t) ω-B i s ω) (gaussianReal 0 t) P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw (B i) P (hB i) s (s+t)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le))
  have hFM : Measurable F := hF.mono ((ginibreBrownianAugmentedFiltration B P hB).le s) le_rfl
  have hInd := ginibreBrownian_augmented_coordinate_increment_independent B P hB hind s t i F hF
  have hp := (hInd.symm.comp (measurable_id.pow_const 2) (show Measurable (fun z : ℝ => z^2) by fun_prop)).integral_mul_eq_mul_integral
    (hFM.pow_const 2).aestronglyMeasurable (hZ.aemeasurable.aestronglyMeasurable.pow 2)
  simp only [Pi.mul_apply, Function.comp_apply, id_eq] at hp
  simp_rw [mul_pow]
  rw [hp, ginibreGaussian_hasLaw_square_mean P _ t hZ, mul_comm]

theorem ginibreBrownian_augmented_linear_memLp_two {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (s t : ℝ≥0) (i : ι) (F : Ω → ℝ)
    (hF : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB s) _ F)
    (hFi : MemLp F 2 P) :
    MemLp (fun ω => F ω*(B i (s+t) ω-B i s ω)) 2 P := by
  have hZ : HasLaw (fun ω => B i (s+t) ω-B i s ω) (gaussianReal 0 t) P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw (B i) P (hB i) s (s+t)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le))
  have hFM : Measurable F := hF.mono ((ginibreBrownianAugmentedFiltration B P hB).le s) le_rfl
  have hInd := ginibreBrownian_augmented_coordinate_increment_independent B P hB hind s t i F hF
  exact ginibreIndependent_predictable_memLp_two P F _ hFM _ hZ hInd id measurable_id hFi
    id measurable_id (IsGaussian.memLp_two_id)

theorem ginibreBrownian_augmented_linear_disjoint_orthogonal {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (s t r v : ℝ≥0) (hst : s+t ≤ r) (i j : ι) (F G : Ω → ℝ)
    (hF : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB s) _ F)
    (hG : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB r) _ G) :
    (∫ ω, (F ω*(B i (s+t) ω-B i s ω))*(G ω*(B j (r+v) ω-B j r ω)) ∂P) = 0 := by
  let H := fun ω => F ω*(B i (s+t) ω-B i s ω)*G ω
  have hsr : s ≤ r := (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le)).trans hst
  have hHM : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB r) _ H :=
    ((hF.mono ((ginibreBrownianAugmentedFiltration B P hB).mono hsr) le_rfl).mul
      ((ginibreBrownian_augmented_coordinate_measurable_at B P hB r (s+t) hst i).sub
        (ginibreBrownian_augmented_coordinate_measurable_at B P hB r s hsr i))).mul hG
  have hH : Measurable H := hHM.mono ((ginibreBrownianAugmentedFiltration B P hB).le r) le_rfl
  have hZ : HasLaw (fun ω => B j (r+v) ω-B j r ω) (gaussianReal 0 v) P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw (B j) P (hB j) r (r+v)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ v from bot_le))
  have hMean : (∫ ω, B j (r+v) ω-B j r ω ∂P) = 0 := by
    have hh := hZ.integral_comp (show AEStronglyMeasurable (id : ℝ → ℝ) (gaussianReal 0 v) by fun_prop)
    simpa using hh.trans (integral_id_gaussianReal (μ := 0) (v := v))
  have hInd := ginibreBrownian_augmented_coordinate_increment_independent B P hB hind r v j H hHM
  have hp := hInd.symm.integral_mul_eq_mul_integral hH.aestronglyMeasurable hZ.aemeasurable.aestronglyMeasurable
  simp only [Pi.mul_apply] at hp
  calc
    _ = ∫ ω, H ω*(B j (r+v) ω-B j r ω) ∂P := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun ω => by dsimp [H]; ring)
    _ = 0 := by rw [hp,hMean,mul_zero]

end
end GinibrePoincare
