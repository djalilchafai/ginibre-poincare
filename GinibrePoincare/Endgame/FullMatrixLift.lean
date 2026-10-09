module

public import GinibrePoincare.Analysis.MatrixSpectralLiftLSIFinite
public import GinibrePoincare.Analysis.MatrixSpectralLiftPoincareFinite
public import GinibrePoincare.Analysis.AlternativeMatrixPoincare
public import GinibrePoincare.Analysis.CorrespondenceMatrixWeakClosure

@[expose] public section

/-! # Matrix-lift inequalities on the finite-overlap domain

The lifted observable is evaluated under the Gaussian matrix law. Its squared
gradient is controlled by the eigenvector-overlap energy; the spectral
pushforward law then returns variance and entropy to the Ginibre measure.
`matrixSpectralLift_finite_overlap_lsi` proves the entropy integrability and
log-Sobolev bound, while the independent Gaussian Poincaré route proves the
variance bound. Both use the same finite-overlap hypothesis.

This endpoint takes overlap integrability explicitly. For the paper's matrix
H¹ formulation, start with `correspondenceMatrix_theorem_1_13` in
`CorrespondenceMatrixWeakClosure`: it derives that integrability from the
matrix weak-gradient hypothesis. These are distinct input interfaces.

Use `fullMatrixLift_named` for named access to the three conclusions.
-/
open MeasureTheory
namespace GinibrePoincare
noncomputable section

theorem fullMatrixLift_functional_inequalities {n : ℕ} (hn : 0 < n)
    (F : Configuration n → ℝ) (hF : ContDiff ℝ 1 F)
    (hsym : ∀ σ : Fin n ≃ Fin n, ∀ z, F (z ∘ σ) = F z)
    (hFL2 : MemLp F 2 (ginibreMeasure n))
    (hE : Integrable (matrixSpectralOverlapEnergy n F) (matrixGaussianMeasure n)) :
    Integrable (fun z => F z ^ 2 * Real.log (F z ^ 2)) (ginibreMeasure n) ∧
      smoothGinibreVariance n F ≤
        (2 / (n : ℝ)) * ∫ A, matrixSpectralOverlapEnergy n F A ∂matrixGaussianMeasure n ∧
      squareEntropy (ginibreMeasure n) F ≤
        (4 / (n : ℝ)) * ∫ A, matrixSpectralOverlapEnergy n F A ∂matrixGaussianMeasure n := by
  obtain ⟨hi, hlsi⟩ := matrixSpectralLift_finite_overlap_lsi hn F
    (hF.differentiable (by norm_num)) hsym hFL2 hE
  exact ⟨hi, matrixSpectralLift_finite_overlap_gaussian_poincare hn F
    (hF.differentiable (by norm_num)) hsym hFL2 hE, hlsi⟩

/-- Variance and entropy bounds with a common matrix overlap energy. -/
structure MatrixLiftInequalities (n : ℕ) (F : Configuration n → ℝ) : Prop where
  /-- The logarithmic integrand in the square entropy is integrable. -/
  entropy_integrable : Integrable (fun z => F z ^ 2 * Real.log (F z ^ 2)) (ginibreMeasure n)
  /-- Gaussian matrix Poincaré transferred through the spectral lift. -/
  poincare : smoothGinibreVariance n F ≤
    (2 / (n : ℝ)) * ∫ A, matrixSpectralOverlapEnergy n F A ∂matrixGaussianMeasure n
  /-- Gaussian matrix log-Sobolev transferred through the same lift. -/
  log_sobolev : squareEntropy (ginibreMeasure n) F ≤
    (4 / (n : ℝ)) * ∫ A, matrixSpectralOverlapEnergy n F A ∂matrixGaussianMeasure n

/-- The finite-overlap matrix inequalities with named conclusions. -/
theorem fullMatrixLift_named {n : ℕ} (hn : 0 < n)
    (F : Configuration n → ℝ) (hF : ContDiff ℝ 1 F)
    (hsym : ∀ σ : Fin n ≃ Fin n, ∀ z, F (z ∘ σ) = F z)
    (hFL2 : MemLp F 2 (ginibreMeasure n))
    (hE : Integrable (matrixSpectralOverlapEnergy n F) (matrixGaussianMeasure n)) :
    MatrixLiftInequalities n F := by
  obtain ⟨hintegrable, hpoincare, hlogSobolev⟩ :=
    fullMatrixLift_functional_inequalities hn F hF hsym hFL2 hE
  exact ⟨hintegrable, hpoincare, hlogSobolev⟩

end
end GinibrePoincare
