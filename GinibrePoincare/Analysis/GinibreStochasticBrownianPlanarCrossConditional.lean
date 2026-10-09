module

public import GinibrePoincare.Analysis.GinibreStochasticBrownianPlanarIncrement
public import GinibrePoincare.Analysis.GinibreStochasticPredictableInnovation
public import GinibrePoincare.Analysis.GinibreStochasticOUPlanarMarkov

@[expose] public section

/-! Actual mixed-coordinate predictable Brownian increments have zero conditional mean. -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem ginibreBrownian_planar_cross_predictable_conditional {Ω : Type*}
    [MeasurableSpace Ω] (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (hind : IndepFun (fun ω u => Br u ω) (fun ω u => Bi u ω) P) (s t : ℝ≥0)
    (F : (Set.Iic s → ℝ) × (Set.Iic s → ℝ) → ℝ) (hF : Measurable F)
    (C : ℝ) (hbound : ∀ p, ‖F p‖ ≤ C) :
    P[(fun ω => F ((fun v => Br v ω), (fun v => Bi v ω))*
        ((Br (s+t) ω-Br s ω)*(Bi (s+t) ω-Bi s ω))) |
      ginibrePlanarBrownianPastMeasurableSpace Br Bi s] =ᵐ[P] (fun _ => 0) := by
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
  have hFi : Integrable (fun ω => F (Past ω)) P := by
    apply (integrable_const C).mono' (hF.comp hPast).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ω => hbound (Past ω)
  let φ : ℝ × ℝ → ℝ := fun z => z.1*z.2
  have hφ : Measurable φ := by fun_prop
  have hφi : Integrable φ ((gaussianReal 0 t).prod (gaussianReal 0 t)) :=
    (IsGaussian.integrable_id (μ := gaussianReal 0 t)).mul_prod IsGaussian.integrable_id
  have hφmean : (∫ z, φ z ∂(gaussianReal 0 t).prod (gaussianReal 0 t)) = 0 := by
    dsimp only [φ]
    rw [integral_prod_mul (fun x : ℝ => x) (fun x : ℝ => x)]
    simp only [integral_id_gaussianReal, mul_zero]
  exact ginibreIndependent_predictable_centered_conditional P Past
    (fun ω => (Br (s+t) ω-Br s ω, Bi (s+t) ω-Bi s ω)) hPast _
    (ginibreBrownian_planar_increment_hasLaw Br Bi P hBr hBi hind s t)
    (ginibreBrownian_planar_increment_independent_past Br Bi P hBr hBi hind s t)
    F hF hFi φ hφ hφi hφmean

end
end GinibrePoincare
