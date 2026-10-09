module

public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityDensityQuotient
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 500000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
  [IsLocallyFiniteMeasure (volume : Measure E)]

theorem ginibreLocalRegularity_local_weak_derivative_unique
    (U : Set E) (hU : IsOpen U) (u g h : E → ℝ) (v : E)
    (hg : MemLp g 2 (volume : Measure E)) (hh : MemLp h 2 volume)
    (hgw : ∀ θ : E → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ U →
      (∫ x, θ x*g x) = -(∫ x, fderiv ℝ θ x v*u x))
    (hhw : ∀ θ : E → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ U →
      (∫ x, θ x*h x) = -(∫ x, fderiv ℝ θ x v*u x)) :
    ∀ᵐ x ∂(volume : Measure E), x ∈ U → g x = h x := by
  have hl := (hg.sub hh).locallyIntegrable (by norm_num) |>.locallyIntegrableOn U
  have hz := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero hl (fun θ hθ hc hs => by
    have hgi := hg.locallyIntegrable (by norm_num) |>.integrable_smul_right_of_hasCompactSupport hθ.continuous hc
    have hhi := hh.locallyIntegrable (by norm_num) |>.integrable_smul_right_of_hasCompactSupport hθ.continuous hc
    have hge : Integrable (fun x => θ x*g x) volume := by
      apply hgi.congr
      exact ae_of_all volume fun x => by dsimp only; simp only [smul_eq_mul]; exact mul_comm _ _
    have hhe : Integrable (fun x => θ x*h x) volume := by
      apply hhi.congr
      exact ae_of_all volume fun x => by dsimp only; simp only [smul_eq_mul]; exact mul_comm _ _
    simp only [Pi.sub_apply, smul_eq_mul, mul_sub]
    rw [integral_sub hge hhe, hgw θ hθ hc hs, hhw θ hθ hc hs, sub_self])
  filter_upwards [hz] with x hx
  intro hu
  exact sub_eq_zero.mp (hx hu)

#print axioms ginibreLocalRegularity_local_weak_derivative_unique
end
end GinibrePoincare
