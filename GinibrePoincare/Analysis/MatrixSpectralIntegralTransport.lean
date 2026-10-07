module

public import GinibrePoincare.Analysis.MatrixGinibreSpectralLaw
public import GinibrePoincare.Analysis.GinibreEntropy

@[expose] public section

open Matrix MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem matrixSpectralLift_integrable_iff {n : ℕ} (hn : 0 < n)
    (F : (Fin n → ℂ) → ℝ) (hF : Measurable F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) :
    Integrable (fun A : Matrix (Fin n) (Fin n) ℂ => F (matrixMeasurableEigenvalues n A)) (matrixGaussianMeasure n) ↔
      Integrable F (ginibreMeasure n) := by
  have hM : Measurable (fun A : Matrix (Fin n) (Fin n) ℂ => F (matrixMeasurableEigenvalues n A)) :=
    hF.comp (matrixMeasurableEigenvalues_measurable n)
  have he := matrixGaussian_symmetric_spectral_lintegral hn
    (fun z => ENNReal.ofReal ‖F z‖) (ENNReal.measurable_ofReal.comp hF.norm)
    (by intro e z; rw [hsym])
  constructor
  · intro h
    refine ⟨hF.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    rw [← he]
    exact (hasFiniteIntegral_iff_norm _).mp h.hasFiniteIntegral
  · intro h
    refine ⟨hM.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    exact he.symm ▸ (hasFiniteIntegral_iff_norm _).mp h.hasFiniteIntegral

theorem matrixSpectralLift_integral {n : ℕ} (hn : 0 < n)
    (F : (Fin n → ℂ) → ℝ) (hF : Measurable F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) :
    ∫ A, F (matrixMeasurableEigenvalues n A) ∂matrixGaussianMeasure n =
      ∫ z, F z ∂ginibreMeasure n := by
  by_cases hi : Integrable F (ginibreMeasure n)
  · have hMi := (matrixSpectralLift_integrable_iff hn F hF hsym).mpr hi
    rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hMi,
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi]
    congr 1
    · exact congrArg ENNReal.toReal (matrixGaussian_symmetric_spectral_lintegral hn
        (fun z => ENNReal.ofReal (F z)) (ENNReal.measurable_ofReal.comp hF)
        (by intro e z; rw [hsym]))
    · exact congrArg ENNReal.toReal (matrixGaussian_symmetric_spectral_lintegral hn
        (fun z => ENNReal.ofReal (-F z)) (ENNReal.measurable_ofReal.comp hF.neg)
        (by intro e z; rw [hsym]))
  · have hMi := mt (matrixSpectralLift_integrable_iff hn F hF hsym).mp hi
    rw [integral_undef hMi, integral_undef hi]


theorem matrixSpectralLift_square_integral {n : ℕ} (hn : 0 < n)
    (F : (Fin n → ℂ) → ℝ) (hF : Measurable F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) :
    ∫ A, F (matrixMeasurableEigenvalues n A) ^ 2 ∂matrixGaussianMeasure n =
      ∫ z, F z ^ 2 ∂ginibreMeasure n :=
  matrixSpectralLift_integral hn (fun z => F z ^ 2) (hF.pow_const 2)
    (by intro e z; rw [hsym])

theorem matrixSpectralLift_squareEntropy {n : ℕ} (hn : 0 < n)
    (F : (Fin n → ℂ) → ℝ) (hF : Measurable F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) :
    squareEntropy (matrixGaussianMeasure n) (fun A => F (matrixMeasurableEigenvalues n A)) =
      squareEntropy (ginibreMeasure n) F := by
  have hs := matrixSpectralLift_square_integral hn F hF hsym
  have hl := matrixSpectralLift_integral hn (fun z => F z ^ 2 * Real.log (F z ^ 2))
    ((hF.pow_const 2).mul (hF.pow_const 2).log) (by intro e z; rw [hsym])
  unfold squareEntropy
  exact congrArg₂ (fun a b : ℝ => a - b * Real.log b) hl hs

theorem matrixSpectralLift_squareLog_integrable_iff {n : ℕ} (hn : 0 < n)
    (F : (Fin n → ℂ) → ℝ) (hF : Measurable F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) :
    Integrable (fun A : Matrix (Fin n) (Fin n) ℂ =>
      F (matrixMeasurableEigenvalues n A) ^ 2 * Real.log (F (matrixMeasurableEigenvalues n A) ^ 2))
      (matrixGaussianMeasure n) ↔
      Integrable (fun z => F z ^ 2 * Real.log (F z ^ 2)) (ginibreMeasure n) :=
  matrixSpectralLift_integrable_iff hn (fun z => F z ^ 2 * Real.log (F z ^ 2))
    ((hF.pow_const 2).mul (hF.pow_const 2).log) (by intro e z; rw [hsym])


theorem matrixSpectralLift_memLp_two_iff {n : ℕ} (hn : 0 < n)
    (F : (Fin n → ℂ) → ℝ) (hF : Measurable F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) :
    MemLp (fun A : Matrix (Fin n) (Fin n) ℂ => F (matrixMeasurableEigenvalues n A)) 2
      (matrixGaussianMeasure n) ↔ MemLp F 2 (ginibreMeasure n) := by
  have hM : Measurable (fun A : Matrix (Fin n) (Fin n) ℂ => F (matrixMeasurableEigenvalues n A)) :=
    hF.comp (matrixMeasurableEigenvalues_measurable n)
  exact (memLp_two_iff_integrable_sq hM.aestronglyMeasurable).trans
    ((matrixSpectralLift_integrable_iff hn (fun z => F z ^ 2) (hF.pow_const 2)
      (by intro e z; rw [hsym])).trans (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).symm)

#print axioms matrixSpectralLift_integral
end
end GinibrePoincare
