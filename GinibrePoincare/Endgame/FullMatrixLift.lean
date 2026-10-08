module

public import GinibrePoincare.Analysis.MatrixSpectralLiftLSIFinite
public import GinibrePoincare.Analysis.MatrixSpectralLiftPoincareFinite
public import GinibrePoincare.Analysis.AlternativeMatrixPoincare
public import GinibrePoincare.Analysis.CorrespondenceMatrixWeakClosure

@[expose] public section

/-! # Both concrete matrix-lift inequalities on the full finite-overlap domain -/
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

end
end GinibrePoincare
