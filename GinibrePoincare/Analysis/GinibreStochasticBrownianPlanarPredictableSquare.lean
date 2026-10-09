module

public import GinibrePoincare.Analysis.GinibreStochasticBrownianPlanarCrossConditional

@[expose] public section

/-! Concrete diagonal quadratic errors with coefficients measurable from the full planar past. -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem ginibreBrownian_planar_predictable_quadratic_secondMoment {Ω : Type*}
    [MeasurableSpace Ω] (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (hind : IndepFun (fun ω u => Br u ω) (fun ω u => Bi u ω) P) (s t : ℝ≥0)
    (F : (Set.Iic s → ℝ) × (Set.Iic s → ℝ) → ℝ) (hF : Measurable F) :
    (∫ ω, (F ((fun v => Br v ω), (fun v => Bi v ω))*
      ((Br (s+t) ω-Br s ω)^2-(t : ℝ)))^2 ∂P) =
      (2*(t : ℝ)^2)*(∫ ω, (F ((fun v => Br v ω), (fun v => Bi v ω)))^2 ∂P) := by
  let := hBr.isGaussianProcess.isProbabilityMeasure
  let Past := fun ω => ((fun v : Set.Iic s => Br v ω), (fun v : Set.Iic s => Bi v ω))
  have hPast : Measurable Past := by
    apply Measurable.prodMk
    · apply measurable_pi_lambda
      intro v
      exact aemeasurable_iff_measurable.mp (hBr.aemeasurable v)
    · apply measurable_pi_lambda
      intro v
      exact aemeasurable_iff_measurable.mp (hBi.aemeasurable v)
  have hZ : HasLaw (fun ω => Br (s+t) ω-Br s ω) (gaussianReal 0 t) P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw Br P hBr.toIsPreBrownianReal s (s+t)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le))
  have hInd := (ginibreBrownian_planar_increment_independent_past Br Bi P hBr hBi hind s t).comp
    measurable_fst measurable_id
  have hMoment : (∫ u : ℝ, (u^2-(t : ℝ))^2 ∂gaussianReal 0 t) = 2*(t : ℝ)^2 := by
    have h := variance_eq_integral (ginibreGaussian_square_memLp_two t).aemeasurable
    rw [ginibreGaussian_secondMoment] at h
    simpa using h.symm.trans (ginibreGaussian_square_variance t)
  have h := ginibreIndependent_predictable_secondMoment P Past (fun ω => Br (s+t) ω-Br s ω)
    hPast (gaussianReal 0 t) hZ hInd F hF (fun u => u^2-(t : ℝ)) (by fun_prop)
  rw [hMoment, mul_comm] at h
  exact h

 theorem ginibreBrownian_planar_predictable_cross_secondMoment {Ω : Type*}
    [MeasurableSpace Ω] (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (hind : IndepFun (fun ω u => Br u ω) (fun ω u => Bi u ω) P) (s t : ℝ≥0)
    (F : (Set.Iic s → ℝ) × (Set.Iic s → ℝ) → ℝ) (hF : Measurable F) :
    (∫ ω, (F ((fun v => Br v ω), (fun v => Bi v ω))*
      ((Br (s+t) ω-Br s ω)*(Bi (s+t) ω-Bi s ω)))^2 ∂P) =
      (t : ℝ)^2*(∫ ω, (F ((fun v => Br v ω), (fun v => Bi v ω)))^2 ∂P) := by
  let := hBr.isGaussianProcess.isProbabilityMeasure
  let Past := fun ω => ((fun v : Set.Iic s => Br v ω), (fun v : Set.Iic s => Bi v ω))
  have hPast : Measurable Past := by
    apply Measurable.prodMk
    · apply measurable_pi_lambda
      intro v
      exact aemeasurable_iff_measurable.mp (hBr.aemeasurable v)
    · apply measurable_pi_lambda
      intro v
      exact aemeasurable_iff_measurable.mp (hBi.aemeasurable v)
  have hMoment : (∫ u : ℝ × ℝ, (u.1*u.2)^2 ∂(gaussianReal 0 t).prod (gaussianReal 0 t)) =
      (t : ℝ)^2 := by
    simp_rw [mul_pow]
    rw [integral_prod_mul (fun u : ℝ => u^2) (fun u : ℝ => u^2), ginibreGaussian_secondMoment]
    norm_num
    ring
  have h := ginibreIndependent_predictable_secondMoment P Past
    (fun ω => (Br (s+t) ω-Br s ω, Bi (s+t) ω-Bi s ω)) hPast _
    (ginibreBrownian_planar_increment_hasLaw Br Bi P hBr hBi hind s t)
    (ginibreBrownian_planar_increment_independent_past Br Bi P hBr hBi hind s t)
    F hF (fun u : ℝ × ℝ => u.1*u.2) (by fun_prop)
  rw [hMoment, mul_comm] at h
  exact h

end
end GinibrePoincare
