module

public import GinibrePoincare.Concrete.GaussianProbability
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

/-! # Factoring coordinatewise integrals under the complex Gaussian product -/

open MeasureTheory
open scoped BigOperators

namespace GinibrePoincare

noncomputable section

theorem integrable_prod_coordinateFunctions_complexGaussianMeasure
    (n : ℕ) (f : Fin n → ℂ → ℂ)
    (hf : ∀ i, Integrable (f i)
      (complexCoordinateGaussianProbability n : Measure ℂ)) :
    Integrable (fun z : Configuration n ↦ ∏ i, f i (z i))
      (complexGaussianMeasure n) := by
  unfold complexGaussianMeasure complexGaussianProbability
  simp only [ProbabilityMeasure.toMeasure_pi]
  exact Integrable.fintype_prod hf

theorem integral_prod_coordinateFunctions_complexGaussianMeasure
    (n : ℕ) (f : Fin n → ℂ → ℂ) :
    (∫ z : Configuration n, ∏ i, f i (z i) ∂complexGaussianMeasure n) =
      ∏ i, ∫ w : ℂ, f i w
        ∂(complexCoordinateGaussianProbability n : Measure ℂ) := by
  unfold complexGaussianMeasure complexGaussianProbability
  simp only [ProbabilityMeasure.toMeasure_pi]
  simpa using (integral_fintype_prod_eq_prod
    (𝕜 := ℂ) (E := fun _ : Fin n ↦ ℂ)
    (μ := fun _ : Fin n ↦
      (complexCoordinateGaussianProbability n : Measure ℂ)) f)

theorem integrable_and_integral_prod_coordinateFunctions_complexGaussianMeasure
    (n : ℕ) (f : Fin n → ℂ → ℂ)
    (hf : ∀ i, Integrable (f i)
      (complexCoordinateGaussianProbability n : Measure ℂ)) :
    Integrable (fun z : Configuration n ↦ ∏ i, f i (z i))
        (complexGaussianMeasure n) ∧
      (∫ z : Configuration n, ∏ i, f i (z i) ∂complexGaussianMeasure n) =
        ∏ i, ∫ w : ℂ, f i w
          ∂(complexCoordinateGaussianProbability n : Measure ℂ) :=
  ⟨integrable_prod_coordinateFunctions_complexGaussianMeasure n f hf,
    integral_prod_coordinateFunctions_complexGaussianMeasure n f⟩

end

end GinibrePoincare
