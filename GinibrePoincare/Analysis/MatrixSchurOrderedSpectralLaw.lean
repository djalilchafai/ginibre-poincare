module

public import GinibrePoincare.Analysis.MatrixSchurSymmetricObservable

@[expose] public section

open Matrix MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

/-- Exact actual Gaussian matrix spectral integration on the ordered chamber.
The remaining scalar is normalized by the same diagonal density at test function one. -/
theorem matrixGaussian_ordered_symmetric_spectral_integral {n : ℕ} (hn : 0 < n) :
    ∃ d : ℝ≥0∞,
      (∀ F : (Fin n → ℂ) → ℝ≥0∞, Measurable F →
        (∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) →
        ∫⁻ A, F (matrixMeasurableEigenvalues n A) ∂matrixGaussianMeasure n =
          d * ∫⁻ z in matrixSchurOrderedConfigurations n, schurDiagonalSpectralDensity n z * F z) ∧
      1 = d * ∫⁻ z in matrixSchurOrderedConfigurations n, schurDiagonalSpectralDensity n z := by
  obtain ⟨c, hc, hnorm⟩ := matrixSchur_gaussian_global_integral hn
  have h : ∀ F : (Fin n → ℂ) → ℝ≥0∞, Measurable F →
      (∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) →
      ∫⁻ A, F (matrixMeasurableEigenvalues n A) ∂matrixGaussianMeasure n =
        (c * schurUpperGaussianDiagonalFactor n) *
          ∫⁻ z in matrixSchurOrderedConfigurations n, schurDiagonalSpectralDensity n z * F z := by
    intro F hF hsym
    have hg := matrixSimpleSymmetricObservable_measurable F hF
    have hi := hc (matrixSimpleSymmetricObservable n F) hg
      (fun U hU A => matrixSimpleSymmetricObservable_unitary F hsym U A hU)
    have ha := lintegral_congr_ae (matrixSimpleSymmetricObservable_ae F)
    rw [ha] at hi
    have hs : (∫⁻ y in matrixSchurSortedUpperDomain n,
        ENNReal.ofReal (vandermondeWeight (fun i => schurUpperCombination y i i)) *
          (matrixGaussianDensity n (schurUpperCombination y) *
            matrixSimpleSymmetricObservable n F (schurUpperCombination y))) =
        ∫⁻ y in matrixSchurSortedUpperDomain n,
          ENNReal.ofReal (vandermondeWeight (fun i => schurUpperCombination y i i)) *
            (matrixGaussianDensity n (schurUpperCombination y) * F (fun i => schurUpperCombination y i i)) := by
      apply setLIntegral_congr_fun (measurableSet_matrixSchurSortedUpperDomain n)
      intro y hy
      exact congrArg (fun v : ℝ≥0∞ =>
        ENNReal.ofReal (vandermondeWeight (fun i => schurUpperCombination y i i)) *
          (matrixGaussianDensity n (schurUpperCombination y) * v))
        (matrixSimpleSymmetricObservable_schurUpper F hsym y hy)
    rw [hs, matrixSchur_sortedUpper_diagonal_integral hn F hF, ← mul_assoc] at hi
    exact hi
  refine ⟨c * schurUpperGaussianDiagonalFactor n, h, ?_⟩
  have h1 := h (fun _ => 1) measurable_const (by intros; rfl)
  simpa only [mul_one, lintegral_const, measure_univ, one_mul] using h1

#print axioms matrixGaussian_ordered_symmetric_spectral_integral
end
end GinibrePoincare
