module

public import GinibrePoincare.Analysis.BrownianAugmentedFreshIncrement
public import GinibrePoincare.Analysis.GinibreStochasticPredictableInnovation
public import GinibrePoincare.Analysis.GinibreStochasticBrownianWeightedQuadratic

@[expose] public section

/-! Exact predictable quadratic moments in the actual augmented joint Brownian filtration. -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem ginibreBrownian_augmented_coordinate_increment_independent {Ω ι A : Type*}
    [MeasurableSpace Ω] [Fintype ι] [MeasurableSpace A]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (s t : ℝ≥0) (i : ι) (Y : Ω → A)
    (hY : @Measurable Ω A (ginibreBrownianAugmentedFiltration B P hB s) _ Y) :
    IndepFun (fun ω => B i (s+t) ω-B i s ω) Y P := by
  have h := brownianFamily_fresh_increment_independent_augmented_variable B P hB hind s t Y hY
  exact h.comp (measurable_pi_apply i) measurable_id

theorem ginibreBrownian_augmented_quadratic_secondMoment {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (s t : ℝ≥0) (i : ι) (F : Ω → ℝ)
    (hF : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB s) _ F) :
    (∫ ω, (F ω*((B i (s+t) ω-B i s ω)^2-(t : ℝ)))^2 ∂P) =
      2*(t : ℝ)^2*(∫ ω, (F ω)^2 ∂P) := by
  let Z := fun ω => B i (s+t) ω-B i s ω
  have hZ : HasLaw Z (gaussianReal 0 t) P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw (B i) P (hB i) s (s+t)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le))
  have hFM : Measurable F := hF.mono (ginibreBrownianAugmentedFiltration B P hB |>.le s) le_rfl
  have hInd := ginibreBrownian_augmented_coordinate_increment_independent B P hB hind s t i F hF
  have hSq := ginibreGaussian_hasLaw_square_memLp_two P Z t hZ
  have hCenter : (∫ ω, ((Z ω)^2-(t : ℝ))^2 ∂P) = 2*(t : ℝ)^2 := by
    have h := variance_eq_integral hSq.aemeasurable
    rw [ginibreGaussian_hasLaw_square_mean P Z t hZ] at h
    exact h.symm.trans (ginibreGaussian_hasLaw_square_variance P Z t hZ)
  have hφ : Measurable (fun z : ℝ => (z^2-(t : ℝ))^2) := by fun_prop
  have hp := (hInd.symm.comp (measurable_id.pow_const 2) hφ).integral_mul_eq_mul_integral
    (hFM.pow_const 2).aestronglyMeasurable ((hφ.comp_aemeasurable hZ.aemeasurable).aestronglyMeasurable)
  simp only [Pi.mul_apply,Function.comp_apply,id_eq] at hp
  dsimp only [Z] at hCenter
  simp_rw [mul_pow]
  rw [hp,hCenter]
  ring

theorem ginibreBrownian_augmented_quadratic_memLp_two {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (s t : ℝ≥0) (i : ι) (F : Ω → ℝ)
    (hF : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB s) _ F)
    (hFi : MemLp F 2 P) :
    MemLp (fun ω => F ω*((B i (s+t) ω-B i s ω)^2-(t : ℝ))) 2 P := by
  have hZ : HasLaw (fun ω => B i (s+t) ω-B i s ω) (gaussianReal 0 t) P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw (B i) P (hB i) s (s+t)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le))
  have hFM : Measurable F := hF.mono (ginibreBrownianAugmentedFiltration B P hB |>.le s) le_rfl
  have hInd := ginibreBrownian_augmented_coordinate_increment_independent B P hB hind s t i F hF
  have hφLp : MemLp (fun z : ℝ => z^2-(t : ℝ)) 2 (gaussianReal 0 t) :=
    (ginibreGaussian_hasLaw_square_memLp_two (gaussianReal 0 t) id t ⟨by fun_prop,by simp⟩).sub (memLp_const _)
  exact ginibreIndependent_predictable_memLp_two P F _ hFM _ hZ hInd id measurable_id hFi
    (fun z => z^2-(t : ℝ)) (by fun_prop) hφLp

end
end GinibrePoincare
