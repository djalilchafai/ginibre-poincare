module

public import GinibrePoincare.Analysis.GinibreHamiltonianInteractionPotential

@[expose] public section

/-! Exact Hamiltonian gradient decomposition for the stationary OU action. -/
open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem ginibreRealCoordinateDifferential_radial {n : ℕ}
    (L : Configuration n →L[ℝ] ℝ) (z : Configuration n) :
    L z = ∑ j : Fin n, ((z j).re*L (realCoordinateDirection j)+
      (z j).im*L (imaginaryCoordinateDirection j)) := by
  have he : z = ∑ j : Fin n, ((z j).re • realCoordinateDirection j+
      (z j).im • imaginaryCoordinateDirection j) := by
    ext i
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply]
    rw [Finset.sum_eq_single i]
    · simp [realCoordinateDirection, imaginaryCoordinateDirection, coordinateDirection,
        Complex.real_smul, Complex.ext_iff]
    · intro b hb hbi
      simp [realCoordinateDirection, imaginaryCoordinateDirection, coordinateDirection, hbi, Ne.symm hbi]
    · simp
  conv_lhs => rw [he]
  rw [map_sum]
  simp only [map_add, map_smul, smul_eq_mul]

def ginibreInteractionGradientNormSq (n : ℕ) (z : Configuration n) : ℝ :=
  ∑ j : Fin n, ((fderiv ℝ (ginibreInteractionPotential n) z (realCoordinateDirection j))^2+
    (fderiv ℝ (ginibreInteractionPotential n) z (imaginaryCoordinateDirection j))^2)

theorem ginibreHamiltonianGradientNormSq_interaction {n : ℕ} (z : Configuration n)
    (hz : CollisionFree z) :
    ginibreHamiltonianGradientNormSq n z = 4*(n : ℝ)^2*configurationNormSq z-
      4*(n : ℝ)*(2*vandermondeDegree n : ℕ)+ginibreInteractionGradientNormSq n z := by
  have hd (j : Fin n) (w : ℂ) :
      fderiv ℝ (ginibreHamiltonian n) z (coordinateDirection j w) =
      2*(n : ℝ)*(conj (z j)*w).re+
        fderiv ℝ (ginibreInteractionPotential n) z (coordinateDirection j w) := by
    rw [fderiv_ginibreHamiltonian_coordinate z hz j w,
      fderiv_configurationNormSq_coordinate, fderiv_ginibreInteractionPotential_coordinate z hz j w]
    ring
  have hEuler := ginibreRealCoordinateDifferential_radial
    (fderiv ℝ (ginibreInteractionPotential n) z) z
  rw [fderiv_ginibreInteractionPotential_radial n z hz] at hEuler
  unfold ginibreHamiltonianGradientNormSq ginibreInteractionGradientNormSq
  simp only [realCoordinateDirection, imaginaryCoordinateDirection, hd, Complex.mul_re,
    Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im,
    mul_one, mul_zero, sub_zero, zero_sub, neg_neg]
  have he (j : Fin n) :
      (2*(n : ℝ)*(z j).re+fderiv ℝ (ginibreInteractionPotential n) z (coordinateDirection j 1))^2+
      (2*(n : ℝ)*(z j).im+fderiv ℝ (ginibreInteractionPotential n) z (coordinateDirection j Complex.I))^2 =
      4*(n : ℝ)^2*((z j).re^2+(z j).im^2)+
      4*(n : ℝ)*((z j).re*fderiv ℝ (ginibreInteractionPotential n) z (realCoordinateDirection j)+
        (z j).im*fderiv ℝ (ginibreInteractionPotential n) z (imaginaryCoordinateDirection j))+
      ((fderiv ℝ (ginibreInteractionPotential n) z (coordinateDirection j 1))^2+
        (fderiv ℝ (ginibreInteractionPotential n) z (coordinateDirection j Complex.I))^2) := by
    simp only [realCoordinateDirection, imaginaryCoordinateDirection]
    ring
  simp_rw [he, Finset.sum_add_distrib,← Finset.mul_sum]
  rw [← hEuler]
  simp only [configurationNormSq, Complex.normSq_apply]
  ring

#print axioms ginibreHamiltonianGradientNormSq_interaction
end
end GinibrePoincare
