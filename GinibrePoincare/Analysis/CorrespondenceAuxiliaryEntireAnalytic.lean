module

public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryHolomorphicFormalSeries
public import GinibrePoincare.Analysis.GaussianEntireSpaceClosure

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- Every actual Gaussian square-integrable entire representative is jointly
complex analytic, proved by its genuine infinite-radius Hermite Taylor series. -/
theorem gaussianEntireRepresentative_complex_analytic {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) (f : Configuration n → ℂ)
    (hf : IsGaussianEntireRepresentative u f) (z : Configuration n) :
    AnalyticAt ℂ f z := by
  let c := fun p : Fin n → ℕ => gaussianHermiteCoefficient hn u (p, 0)
  have hcoef : ∀ p, ‖c p‖ ≤ ‖u‖ := fun p => gaussianHermiteCoefficient_norm_le hn u (p, 0)
  have hseries := gaussianZeroMode_holomorphic_series_ae hn u
  rw [gaussianEntireRepresentative_zeroMode_eq hn u f hf] at hseries
  have heq : (fun w => ∑' p, c p * ComplexHermite.multivariateNormalized n hn p 0 w) = f :=
    continuous_eq_of_ae_eq_complexGaussian hn
      (differentiable_holomorphicHermite_series n hn c hcoef).continuous hf.1.continuous
      (hseries.trans hf.2.symm)
  rw [← heq]
  have hr := holomorphicHermiteFormalSeries_radius n c hcoef
  have ha := (holomorphicHermiteFormalSeries n c).analyticOnNhd z (by simp [hr])
  have he := funext (holomorphicHermiteFormalSeries_sum n hn c hcoef)
  rw [he] at ha
  exact ha

/-- Restriction of the actual complex Taylor series to real coordinates. -/
theorem gaussianEntireRepresentative_real_analytic {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) (f : Configuration n → ℂ)
    (hf : IsGaussianEntireRepresentative u f) (z : Configuration n) :
    AnalyticAt ℝ f z :=
  (gaussianEntireRepresentative_complex_analytic hn u f hf z).restrictScalars

#print axioms gaussianEntireRepresentative_complex_analytic
#print axioms gaussianEntireRepresentative_real_analytic
end
end GinibrePoincare
