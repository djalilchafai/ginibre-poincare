module

public import GinibrePoincare.Analysis.GinibreHamiltonianGaussianOUContinuousReversal
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

open Set MeasureTheory ProbabilityTheory
namespace GinibrePoincare
noncomputable section

theorem invariant_measure_withDensity_of_invariant_weight
    {E : Type*} [MeasurableSpace E] (μ : Measure E) (R : E → E)
    (hR : Measurable R) (hμ : μ.map R=μ) (w : E → ENNReal)
    (hw : Measurable w) (hwr : ∀ x, w (R x)=w x) :
    (μ.withDensity w).map R=μ.withDensity w := by
  ext s hs
  rw [Measure.map_apply hR hs,withDensity_apply _ (hR hs),withDensity_apply _ hs]
  have hm : Measurable (s.indicator w) := hw.indicator hs
  have he : (R ⁻¹' s).indicator w = (s.indicator w) ∘ R := by
    funext x
    by_cases h : R x ∈ s
    · simp [h,hwr]
    · simp [h]
  rw [← lintegral_indicator (hR hs),he]
  simp only [Function.comp_apply]
  rw [← lintegral_map hm hR]
  rw [hμ,lintegral_indicator hs]

def gradientPathReversalWeight {E : Type*} (T : ℝ) (V A : E → ℝ) (x : ℝ → E) : ENNReal :=
  ENNReal.ofReal (Real.exp (-(V (x 0)+V (x T))/2 + ∫ s in (0 : ℝ)..T, A (x s)))

theorem gradientPathReversalWeight_reverse {E : Type*} (T : ℝ) (V A : E → ℝ) (x : ℝ → E) :
    gradientPathReversalWeight T V A (fun s => x (T-s)) = gradientPathReversalWeight T V A x := by
  unfold gradientPathReversalWeight
  have hi := intervalIntegral.integral_comp_sub_left (fun s => A (x s)) (a := 0) (b := T) T
  simp only [sub_self,sub_zero] at hi ⊢
  rw [hi]
  congr 2
  ring

end
end GinibrePoincare
