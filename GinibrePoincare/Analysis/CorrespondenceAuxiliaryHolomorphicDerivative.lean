module

public import GinibrePoincare.Analysis.HermiteRodriguesHolomorphicLowering
public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

@[expose] public section
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem dholComponent_eq_complex_fderiv {n : ℕ} {f : Configuration n → ℂ}
    {z : Configuration n} (hf : DifferentiableAt ℂ f z) (j : Fin n) :
    ComplexHermite.dholComponent f j z = fderiv ℂ f z (realCoordinateDirection j) := by
  have hi : imaginaryCoordinateDirection j = Complex.I • realCoordinateDirection j := by
    funext k
    simp [imaginaryCoordinateDirection, realCoordinateDirection, coordinateDirection, Pi.smul_apply]
  unfold ComplexHermite.dholComponent
  rw [hf.fderiv_restrictScalars (𝕜 := ℝ)]
  change (1/2 : ℂ)*((fderiv ℂ f z) (realCoordinateDirection j) -
    Complex.I * (fderiv ℂ f z) (imaginaryCoordinateDirection j)) = _
  rw [hi, map_smul]
  simp only [smul_eq_mul,← mul_assoc, Complex.I_mul_I, neg_one_mul]
  ring

theorem fderiv_holomorphicHermite_coordinate (n : ℕ) (hn : 0 < n)
    (p : Fin n → ℕ) (j : Fin n) (z : Configuration n) :
    fderiv ℂ (ComplexHermite.multivariateNormalized n hn p 0) z
        (realCoordinateDirection j) =
      (Real.sqrt (n*p j : ℕ) : ℂ) *
        ComplexHermite.multivariateNormalized n hn (ComplexHermite.lowerAt p j) 0 z := by
  have hd : DifferentiableAt ℂ (ComplexHermite.multivariateNormalized n hn p 0) z := by
    change DifferentiableAt ℂ (fun w => ComplexHermite.multivariateNormalized n hn p 0 w) z
    simp only [ComplexHermite.multivariateNormalized_zero_right]
    fun_prop
  rw [← dholComponent_eq_complex_fderiv hd j]
  exact ComplexHermite.dholComponent_multivariateNormalized n hn p 0 j z

#print axioms dholComponent_eq_complex_fderiv
#print axioms fderiv_holomorphicHermite_coordinate
end
end GinibrePoincare
