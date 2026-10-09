module

public import GinibrePoincare.Analysis.GinibreStochasticAugmentedPredictableQuadratic

@[expose] public section

/-! Genuine orthogonality of disjoint predictable quadratic innovations in the augmented joint past. -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem ginibreBrownian_augmented_coordinate_measurable_at {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (r v : ℝ≥0) (hvr : v ≤ r) (i : ι) :
    @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB r) _ (B i v) := by
  have h := (ginibreBrownianFamilyFiltration_coordinate_stronglyAdapted B P hB i v).measurable
  exact h.mono ((ginibreBrownianFamilyPastSpace_mono B hvr).trans
    (ginibreNullAugmentation_base_le P (ginibreBrownianFamilyPastSpace B r))) le_rfl

theorem ginibreBrownian_augmented_quadratic_disjoint_orthogonal {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (s t r v : ℝ≥0) (hst : s+t ≤ r) (i j : ι) (F G : Ω → ℝ)
    (hF : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB s) _ F)
    (hG : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB r) _ G) :
    (∫ ω, (F ω*((B i (s+t) ω-B i s ω)^2-(t : ℝ)))*
      (G ω*((B j (r+v) ω-B j r ω)^2-(v : ℝ))) ∂P) = 0 := by
  let H := fun ω => F ω*((B i (s+t) ω-B i s ω)^2-(t : ℝ))*G ω
  have hsr : s ≤ r := (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le)).trans hst
  have hHM : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB r) _ H :=
    ((hF.mono ((ginibreBrownianAugmentedFiltration B P hB).mono hsr) le_rfl).mul
      (((ginibreBrownian_augmented_coordinate_measurable_at B P hB r (s+t) hst i).sub
        (ginibreBrownian_augmented_coordinate_measurable_at B P hB r s hsr i)).pow_const 2 |>.sub measurable_const)).mul hG
  have hH : Measurable H := hHM.mono ((ginibreBrownianAugmentedFiltration B P hB).le r) le_rfl
  let Z := fun ω => B j (r+v) ω-B j r ω
  have hZ : HasLaw Z (gaussianReal 0 v) P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw (B j) P (hB j) r (r+v)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ v from bot_le))
  have hSq := ginibreGaussian_hasLaw_square_memLp_two P Z v hZ
  have hMean : (∫ ω, ((Z ω)^2-(v : ℝ)) ∂P) = 0 := by
    rw [integral_sub (hSq.integrable (by norm_num)) (integrable_const _), ginibreGaussian_hasLaw_square_mean P Z v hZ]
    simp
  have hInd := ginibreBrownian_augmented_coordinate_increment_independent B P hB hind r v j H hHM
  have hφ : Measurable (fun z : ℝ => z^2-(v : ℝ)) := by fun_prop
  have hp := (hInd.symm.comp measurable_id hφ).integral_mul_eq_mul_integral
    hH.aestronglyMeasurable (hφ.comp_aemeasurable hZ.aemeasurable).aestronglyMeasurable
  simp only [Function.comp_apply, Pi.mul_apply, id_eq] at hp
  dsimp only [Z] at hMean
  calc
    _ = ∫ ω, H ω*((B j (r+v) ω-B j r ω)^2-(v : ℝ)) ∂P := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun ω => by dsimp [H]; ring)
    _ = 0 := by rw [hp, hMean, mul_zero]

end
end GinibrePoincare
