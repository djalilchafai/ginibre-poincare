module
public import GinibrePoincare.Analysis.GinibreSymmetricWeakPoincare

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem correspondence_standardGaussian_cross_moment :
    (∫ z : ℂ, z.re*z.im ∂standardComplexGaussianMeasure) = 0 := by
  have hi : Integrable (fun z : ℂ => z^2) standardComplexGaussianMeasure := by
    simpa [standardComplexGaussianMeasure, complexGaussianMixedMoment] using
      integrable_mixedComplexMonomial 1 2 0
  have hm : (∫ z : ℂ, z^2 ∂standardComplexGaussianMeasure) = 0 := by
    have h := complexGaussianMixedMoment_formula (by norm_num : (0 : ℕ) < 1) 2 0
    simpa [standardComplexGaussianMeasure, complexGaussianMixedMoment] using h
  have he (z : ℂ) : z.re*z.im = (1/2 : ℝ)*(z^2).im := by
    simp [pow_two, Complex.mul_im]
    ring
  simp_rw [he]
  rw [integral_const_mul]
  have him : (∫ z : ℂ, (z^2).im ∂standardComplexGaussianMeasure) = 0 := by
    calc
      _ = (∫ z : ℂ, z^2 ∂standardComplexGaussianMeasure).im := integral_im hi
      _ = 0 := by rw [hm]; rfl
  rw [him]
  simp

/-- Literal zero cross-covariance of the two centered components in (2.34). -/
theorem correspondence_coordinateSum_cross_covariance (n : ℕ) (hn : 0 < n) :
    (∫ z : Configuration n, (coordinateSum z).re*(coordinateSum z).im ∂ginibreMeasure n) = 0 := by
  have hm := integral_map (μ := ginibreMeasure n)
    (measurable_coordinateSum n).aemeasurable
    (Complex.continuous_re.mul Complex.continuous_im).aestronglyMeasurable
  change (∫ z : Configuration n, (Complex.re * Complex.im) (coordinateSum z) ∂ginibreMeasure n) = 0
  rw [← hm, coordinateSum_ginibre_gaussian n hn]
  exact correspondence_standardGaussian_cross_moment

#print axioms correspondence_coordinateSum_cross_covariance
end
end GinibrePoincare
