module

public import GinibrePoincare.Analysis.GinibreStochasticOrthogonalSquareSum

@[expose] public section

/-! Actual predictable Brownian increment square moments and orthogonality. -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem ginibreBrownian_predictable_linear_secondMoment {Ω : Type*}
    [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : IsBrownianReal B P) (s t : ℝ≥0)
    (F : (Set.Iic s → ℝ) → ℝ) (hF : Measurable F) :
    (∫ ω, (F (fun v => B v ω)*(B (s+t) ω-B s ω))^2 ∂P) =
      (t : ℝ)*(∫ ω, (F (fun v => B v ω))^2 ∂P) := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hPast : Measurable (fun ω (v : Set.Iic s) => B v ω) := by
    apply measurable_pi_lambda
    intro v
    exact aemeasurable_iff_measurable.mp (hB.aemeasurable v)
  have hZ : HasLaw (fun ω => B (s+t) ω-B s ω) (gaussianReal 0 t) P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw B P hB.toIsPreBrownianReal s (s+t)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le))
  have hInd := (ginibreBrownian_increment_whole_past_independent B P hB.toIsPreBrownianReal s t).symm.comp
    (hF.pow_const 2) (show Measurable (fun z : ℝ => z^2) by fun_prop)
  have hp := hInd.integral_mul_eq_mul_integral
    ((hF.comp hPast).pow_const 2).aestronglyMeasurable (hZ.aemeasurable.aestronglyMeasurable.pow 2)
  simp only [Pi.mul_apply, Function.comp_apply] at hp
  simp_rw [mul_pow]
  rw [hp, ginibreGaussian_hasLaw_square_mean P _ t hZ, mul_comm]

theorem ginibreBrownian_predictable_linear_memLp_two {Ω : Type*}
    [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : IsBrownianReal B P) (s t : ℝ≥0)
    (F : (Set.Iic s → ℝ) → ℝ) (hF : Measurable F) (C : ℝ) (hbound : ∀ p, ‖F p‖ ≤ C) :
    MemLp (fun ω => F (fun v => B v ω)*(B (s+t) ω-B s ω)) 2 P := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hPast : Measurable (fun ω (v : Set.Iic s) => B v ω) := by
    apply measurable_pi_lambda
    intro v
    exact aemeasurable_iff_measurable.mp (hB.aemeasurable v)
  have hZ : HasLaw (fun ω => B (s+t) ω-B s ω) (gaussianReal 0 t) P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw B P hB.toIsPreBrownianReal s (s+t)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le))
  have hm : MemLp (fun ω => B (s+t) ω-B s ω) 2 P := by
    have h : MemLp id 2 (gaussianReal 0 t) := IsGaussian.memLp_two_id
    rw [← hZ.map_eq] at h
    exact (memLp_map_measure_iff (by fun_prop) hZ.aemeasurable).mp h
  have hW : AEStronglyMeasurable (fun ω => F (fun v => B v ω)) P :=
    (hF.comp hPast).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq (hW.mul hm.aestronglyMeasurable)).mpr
  change Integrable (fun ω => (F (fun v => B v ω)*(B (s+t) ω-B s ω))^2) P
  simp_rw [mul_pow]
  apply hm.integrable_sq.bdd_mul (c := C^2) (hW.pow 2)
  apply Eventually.of_forall
  intro ω
  change ‖(F (fun v => B v ω))^2‖ ≤ C^2
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hbound _) 2

end
end GinibrePoincare
