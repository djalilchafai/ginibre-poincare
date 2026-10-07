module

public import Mathlib.Probability.Martingale.OptionalSampling
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

@[expose] public section

/-! Honest bounded optional sampling for countable-range continuous-time stops. -/
open MeasureTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem martingale_integral_stoppedValue_of_countable_range
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M ℱ μ) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    {T : ℝ≥0} (hτT : ∀ ω, τ ω ≤ T) (hc : (Set.range τ).Countable) :
    ∫ ω, stoppedValue M τ ω ∂μ = ∫ ω, M 0 ω ∂μ := by
  have he := hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range hτ hτT hc
  rw [integral_congr_ae he, integral_condExp (hτ.measurableSpace_le_of_le hτT)]
  have h0 := hM.condExp_ae_eq (show (0 : ℝ≥0) ≤ T from bot_le)
  exact (integral_condExp (ℱ.le 0)).symm.trans (integral_congr_ae h0)

 theorem martingale_integrable_stoppedValue_of_countable_range
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M ℱ μ) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    {T : ℝ≥0} (hτT : ∀ ω, τ ω ≤ T) (hc : (Set.range τ).Countable) :
    Integrable (stoppedValue M τ) μ := by
  exact (integrable_condExp : Integrable (μ[M T | hτ.measurableSpace]) μ).congr
    (hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range hτ hτT hc).symm

end
end GinibrePoincare
