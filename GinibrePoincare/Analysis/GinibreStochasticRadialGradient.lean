module

public import GinibrePoincare.Analysis.GinibreStochasticCIRGenerator
public import GinibrePoincare.Analysis.GinibreStochasticRadialDirection
public import GinibrePoincare.Analysis.RadiusGradient

@[expose] public section

/-! Exact real radial gradients underlying the actual CIR noise coefficient. -/
open scoped Topology ComplexConjugate
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000

theorem ginibre_fderiv_complexRadius_ofReal (n : ℕ) (z v : Configuration n) :
    fderiv ℝ (complexRadius n) z v = (fderiv ℝ pairwiseRadius z v : ℂ) := by
  have hd : DifferentiableAt ℝ (pairwiseRadius : Configuration n → ℝ) z :=
    (ginibre_contDiff_pairwiseRadius n).differentiable (by simp) z
  have h := (Complex.ofRealCLM.hasFDerivAt.comp z hd.hasFDerivAt).fderiv
  exact congrArg (fun L : Configuration n →L[ℝ] ℂ => L v) h

theorem ginibre_fderiv_pairwiseRadius_real (n : ℕ) (z : Configuration n) (j : Fin n) :
    fderiv ℝ pairwiseRadius z (realCoordinateDirection j) = 2*(centeredScaled z j).re := by
  have h := congrArg Complex.re (radius_gradient_real n z j)
  rw [ginibre_fderiv_complexRadius_ofReal] at h
  simpa [two_mul] using h

theorem ginibre_fderiv_pairwiseRadius_imaginary (n : ℕ) (z : Configuration n) (j : Fin n) :
    fderiv ℝ pairwiseRadius z (imaginaryCoordinateDirection j) = 2*(centeredScaled z j).im := by
  have h := congrArg Complex.re (radius_gradient_imaginary n z j)
  rw [ginibre_fderiv_complexRadius_ofReal] at h
  simpa [two_mul] using h

theorem ginibre_pairwiseRadius_gradient_normSq (n : ℕ) (z : Configuration n) :
    (∑ j : Fin n,
      ((fderiv ℝ pairwiseRadius z (realCoordinateDirection j))^2+
      (fderiv ℝ pairwiseRadius z (imaginaryCoordinateDirection j))^2)) =
      4*(n : ℝ)*pairwiseRadius z := by
  have h : (∑ j : Fin n, Complex.normSq (centeredScaled z j)) =
      (n : ℝ)*pairwiseRadius z := by
    have h := congrArg Complex.re (centeredScaled_norm_sum n z)
    simpa [Complex.mul_conj,complexRadius] using h
  simp_rw [ginibre_fderiv_pairwiseRadius_real,ginibre_fderiv_pairwiseRadius_imaginary]
  calc
    _ = 4*∑ j : Fin n, Complex.normSq (centeredScaled z j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Complex.normSq_apply]
      ring
    _ = _ := by rw [h];ring

theorem centeredScaled_eq_recentered {n : ℕ} (hn : 0 < n)
    (z : Configuration n) (j : Fin n) :
    centeredScaled z j = (n : ℂ)*recenteredConfiguration n z j := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [centeredScaled,recenteredConfiguration,projectToOrthogonal]
  field_simp

theorem ginibre_fderiv_pairwiseRadius_coordinate {n : ℕ} (hn : 0 < n)
    (z : Configuration n) (i : Fin n × Fin 2) :
    fderiv ℝ pairwiseRadius z (ginibreCoordinateDirection i) =
      2*(n : ℝ)*configurationEuclideanEquiv n (recenteredConfiguration n z) i := by
  rcases i with ⟨j,k⟩
  fin_cases k
  · change fderiv ℝ pairwiseRadius z (realCoordinateDirection j) =
      2*(n : ℝ)*configurationEuclideanEquiv n (recenteredConfiguration n z) (j,0)
    rw [ginibre_fderiv_pairwiseRadius_real,centeredScaled_eq_recentered hn]
    simp [Complex.mul_re] <;> ring
  · change fderiv ℝ pairwiseRadius z (imaginaryCoordinateDirection j) =
      2*(n : ℝ)*configurationEuclideanEquiv n (recenteredConfiguration n z) (j,1)
    rw [ginibre_fderiv_pairwiseRadius_imaginary,centeredScaled_eq_recentered hn]
    simp [Complex.mul_im] <;> ring

theorem ginibre_configurationEuclidean_norm_sq (n : ℕ) (z : Configuration n) :
    ‖configurationEuclideanEquiv n z‖^2=configurationNormSq z := by
  rw [EuclideanSpace.real_norm_sq_eq,Fintype.sum_prod_type]
  simp [Fin.sum_univ_two,configurationNormSq,Complex.normSq_apply,pow_two]

end
end GinibrePoincare
