module

public import GinibrePoincare.Analysis.MatrixSpectralLaw

@[expose] public section

open Matrix MeasureTheory
open scoped ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem matrix_charpoly_fin_one (A : Matrix (Fin 1) (Fin 1) ℂ) :
    A.charpoly = Polynomial.X - Polynomial.C (A 0 0) := by
  have hA : A = Matrix.diagonal (fun _ : Fin 1 => A 0 0) := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  rw [hA, Matrix.charpoly_diagonal]
  simp

theorem matrixMeasurableEigenvalues_one (A : GinibreMatrixCoordinates 1) :
    matrixMeasurableEigenvalues 1 A = A 0 := by
  have hs : (Matrix.of A).charpoly.Separable := by
    rw [matrix_charpoly_fin_one]
    exact Polynomial.separable_X_sub_C
  have hr := (matrixMeasurableEigenvalues_spec 1 A hs).2 0
  rw [matrix_charpoly_fin_one] at hr
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hr
  funext i
  fin_cases i
  exact sub_eq_zero.mp hr

/-- The spectral pushforward coincides with the normalized complex Gaussian law
in the one-dimensional base case. -/
theorem matrixSpectralMeasure_one_eq_complexGaussian :
    matrixSpectralMeasure 1 = complexGaussianMeasure 1 := by
  have hf : matrixMeasurableEigenvalues 1 = fun A : GinibreMatrixCoordinates 1 => A 0 :=
    funext matrixMeasurableEigenvalues_one
  rw [matrixSpectralMeasure, hf]
  have hp := measurePreserving_eval
    (fun _ : Fin 1 => (complexGaussianProbability 1 : Measure (Fin 1 → ℂ))) 0
  exact hp.map_eq

#print axioms matrixSpectralMeasure_one_eq_complexGaussian

theorem matrixSpectralMeasure_one_eq_ginibre : matrixSpectralMeasure 1 = ginibreMeasure 1 := by
  have hd : (vandermondeDensity : Configuration 1 → ℝ≥0∞) = 1 := by
    funext z
    simp [vandermondeDensity, vandermondeWeight, vandermonde]
  have hr : rawGinibreMeasure 1 = complexGaussianMeasure 1 := by
    rw [rawGinibreMeasure, hd, withDensity_one]
  rw [ginibreMeasure, ginibreNormalizingMass, hr, complexGaussianMeasure_univ]
  simp only [inv_one, one_smul]
  exact matrixSpectralMeasure_one_eq_complexGaussian

#print axioms matrixSpectralMeasure_one_eq_ginibre
end
end GinibrePoincare
