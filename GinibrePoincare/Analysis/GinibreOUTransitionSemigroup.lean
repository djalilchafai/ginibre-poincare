module

public import GinibrePoincare.Analysis.GinibreOUTransition
public import Mathlib.Probability.Kernel.Composition.Comp

@[expose] public section

/-! # Genuine Chapman–Kolmogorov identity for OU transition kernels -/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem ginibreOUTransition_lintegral_noise (rate t : ℝ≥0) (x : ℝ)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ y, f y ∂ginibreOUTransition rate t x) =
      ∫⁻ y, f (ginibreOUDecay rate t * x + y) ∂gaussianReal 0 (ginibreOUVariance rate t) := by
  change (∫⁻ y, f y ∂gaussianReal (ginibreOUDecay rate t * x) (ginibreOUVariance rate t)) = _
  have hg : (gaussianReal 0 (ginibreOUVariance rate t)).map
      (fun y => ginibreOUDecay rate t * x + y) =
      gaussianReal (ginibreOUDecay rate t * x) (ginibreOUVariance rate t) := by
    simpa using gaussianReal_map_const_add (μ := 0) (v := ginibreOUVariance rate t)
      (ginibreOUDecay rate t * x)
  rw [← hg, lintegral_map hf (by fun_prop)]

/-- The actual probability kernels satisfy the semigroup law on all
measurable observables, including time zero. -/
theorem ginibreOUTransition_comp (rate s t : ℝ≥0) :
    ginibreOUTransition rate t ∘ₖ ginibreOUTransition rate s =
      ginibreOUTransition rate (s + t) := by
  apply Kernel.ext_fun
  intro x f hf
  rw [Kernel.lintegral_comp _ _ _ hf]
  simp_rw [ginibreOUTransition_lintegral_noise rate t _ f hf]
  have hm : Measurable (fun y : ℝ => ∫⁻ z,
      f (ginibreOUDecay rate t * y + z) ∂gaussianReal 0 (ginibreOUVariance rate t)) :=
    Measurable.lintegral_prod_right (hf.comp (by fun_prop))
  rw [ginibreOUTransition_lintegral_noise rate s x _ hm]
  have hp : Measurable (fun p : ℝ × ℝ =>
      f (ginibreOUDecay rate t * (ginibreOUDecay rate s * x + p.1) + p.2)) :=
    hf.comp (by fun_prop)
  rw [← lintegral_prod _ hp.aemeasurable]
  rw [← lintegral_map hf (by fun_prop), ginibreOUTransition_two_steps]

/-- The actual stationary real Gaussian law is preserved by each OU kernel. -/
theorem ginibreOUTransition_stationary (rate t : ℝ≥0) :
    (gaussianReal 0 (1 / 2)).bind (ginibreOUTransition rate t) = gaussianReal 0 (1 / 2) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [Measure.lintegral_bind (ginibreOUTransition rate t).aemeasurable hf.aemeasurable]
  simp_rw [ginibreOUTransition_lintegral_noise rate t _ f hf]
  have hp : Measurable (fun p : ℝ × ℝ => f (ginibreOUDecay rate t * p.1 + p.2)) :=
    hf.comp (by fun_prop)
  rw [← lintegral_prod _ hp.aemeasurable, ← lintegral_map hf (by fun_prop)]
  have hlaw := ginibreGaussian_affine_product_map (ginibreOUDecay rate t) 0
    (1 / 2) (ginibreOUVariance rate t)
  simp only [add_zero] at hlaw
  rw [hlaw]
  have hv : NNReal.mk (ginibreOUDecay rate t ^ 2) (sq_nonneg _) * (1 / 2) +
      ginibreOUVariance rate t = (1 / 2 : ℝ≥0) := by
    apply Subtype.ext
    change ginibreOUDecay rate t ^ 2 * (1 / 2) + (ginibreOUVariance rate t : ℝ) = 1 / 2
    rw [ginibreOUVariance_coe]
    ring
  rw [hv]

end
end GinibrePoincare
