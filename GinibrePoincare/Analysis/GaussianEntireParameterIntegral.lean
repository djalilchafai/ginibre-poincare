module

public import GinibrePoincare.Analysis.GaussianEntireRegularity
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff Interval
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000

/-- Continuous parameterized derivatives give holomorphic interval
integrals. Compactness supplies the domination bound automatically. -/
theorem gaussian_entire_parameter_intervalIntegral {n : ℕ}
    (F : Configuration n → ℝ → ℂ)
    (F' : Configuration n → ℝ → Configuration n →L[ℂ] ℂ)
    (hF : Continuous ↿F) (hF' : Continuous ↿F')
    (hd : ∀ z t, HasFDerivAt (fun w => F w t) (F' z t) z) (a b : ℝ) :
    Differentiable ℂ (fun z => ∫ t in a..b, F z t) := by
  intro z
  have hK : IsCompact (closedBall z (1 : ℝ) ×ˢ uIcc a b) :=
    (isCompact_closedBall z 1).prod isCompact_uIcc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF'.continuousOn
  have hc : ∀ w, Continuous (F w) := fun w => hF.comp (continuous_const.prodMk continuous_id)
  have hc' : Continuous (F' z) := hF'.comp (continuous_const.prodMk continuous_id)
  have hi := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume) (a := a) (b := b)
    (F := F) (F' := F') (s := ball z 1) (x₀ := z) (bound := fun _ => C)
    (ball_mem_nhds z (by norm_num))
    (Eventually.of_forall (fun w => (hc w).aestronglyMeasurable))
    ((hc z).intervalIntegrable a b) hc'.aestronglyMeasurable
    (Eventually.of_forall (fun t ht w hw =>
      hC (w, t) ⟨ball_subset_closedBall hw, uIoc_subset_uIcc ht⟩))
    intervalIntegrable_const
    (Eventually.of_forall (fun t _ w _ => hd w t))
  exact hi.differentiableAt

#print axioms gaussian_entire_parameter_intervalIntegral

end
end GinibrePoincare
