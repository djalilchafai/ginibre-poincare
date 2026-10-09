module

public import GinibrePoincare.Analysis.GaussianEntireRegularity
public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryHolomorphicDerivative
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Entire functions satisfy the literal all-coordinate distributional
Cauchy–Riemann equations against ordinary compact smooth real tests. -/
theorem entire_compact_CR_test {n : ℕ} (F : Configuration n → ℂ)
    (hF : Differentiable ℂ F) (θ : Configuration n → ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ) (j : Fin n) :
    (∫ z, F z * ((fderiv ℝ θ z (realCoordinateDirection j) : ℂ) +
      Complex.I * (fderiv ℝ θ z (imaginaryCoordinateDirection j) : ℂ))) = 0 := by
  have hFR := gaussian_entire_contDiff_real_one hF
  have hθR := hθ.differentiable (by simp)
  have hcontDθ (v : Configuration n) : Continuous (fun z => fderiv ℝ θ z v) :=
    (hθ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcontDF (v : Configuration n) : Continuous (fun z => fderiv ℝ F z v) :=
    (hFR.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have h1 (v : Configuration n) : Integrable (fun z => fderiv ℝ θ z v • F z) volume :=
    ((hcontDθ v).smul hF.continuous).integrable_of_hasCompactSupport
      ((hc.fderiv_apply ℝ v).smul_right)
  have h2 (v : Configuration n) : Integrable (fun z => θ z • fderiv ℝ F z v) volume :=
    (hθ.continuous.smul (hcontDF v)).integrable_of_hasCompactSupport hc.smul_right
  have h3 : Integrable (fun z => θ z • F z) volume :=
    (hθ.continuous.smul hF.continuous).integrable_of_hasCompactSupport hc.smul_right
  have hibp (v : Configuration n) :
      (∫ z, fderiv ℝ θ z v • F z) = -(∫ z, θ z • fderiv ℝ F z v) := by
    have hh := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
      (h1 v) (h2 v) h3 (fun z _ => hθR z)
      (fun z _ => hFR.differentiable (by norm_num) z)
    simpa only [neg_neg] using congrArg Neg.neg hh.symm
  have hpoint (z : Configuration n) : fderiv ℝ F z (realCoordinateDirection j) +
      Complex.I * fderiv ℝ F z (imaginaryCoordinateDirection j) = 0 := by
    rw [(hF z).fderiv_restrictScalars (𝕜 := ℝ)]
    have hi : imaginaryCoordinateDirection j = Complex.I • realCoordinateDirection j := by
      funext k
      simp [imaginaryCoordinateDirection, realCoordinateDirection, coordinateDirection, Pi.smul_apply]
    change fderiv ℂ F z (realCoordinateDirection j) +
      Complex.I * fderiv ℂ F z (imaginaryCoordinateDirection j) = 0
    rw [hi, map_smul]
    simp only [smul_eq_mul,← mul_assoc, Complex.I_mul_I, neg_one_mul, add_neg_cancel]
  have hfunc : (fun z => F z * ((fderiv ℝ θ z (realCoordinateDirection j) : ℂ) +
      Complex.I*(fderiv ℝ θ z (imaginaryCoordinateDirection j) : ℂ))) =
      (fun z => fderiv ℝ θ z (realCoordinateDirection j) • F z +
        Complex.I*(fderiv ℝ θ z (imaginaryCoordinateDirection j) • F z)) := by
    funext z
    simp only [Complex.real_smul]
    ring
  rw [hfunc, integral_add (h1 _) ((h1 _).const_mul _), integral_const_mul, hibp, hibp]
  rw [mul_neg,← neg_add,← integral_const_mul,← integral_add (h2 _) ((h2 _).const_mul _)]
  have hz : (∫ z, θ z • fderiv ℝ F z (realCoordinateDirection j) +
      Complex.I*(θ z • fderiv ℝ F z (imaginaryCoordinateDirection j))) = 0 := by
    have hzero : ∀ z, θ z • fderiv ℝ F z (realCoordinateDirection j) +
        Complex.I*(θ z • fderiv ℝ F z (imaginaryCoordinateDirection j)) = 0 := by
      intro z
      rw [Complex.real_smul, Complex.real_smul]
      calc
        _ = (θ z : ℂ)*(fderiv ℝ F z (realCoordinateDirection j) +
          Complex.I*fderiv ℝ F z (imaginaryCoordinateDirection j)) := by ring
        _ = 0 := by rw [hpoint, mul_zero]
    simp only [hzero, integral_zero]
  rw [hz, neg_zero]

#print axioms entire_compact_CR_test
end
end GinibrePoincare
