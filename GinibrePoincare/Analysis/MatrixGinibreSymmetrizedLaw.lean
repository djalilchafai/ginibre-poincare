module

public import GinibrePoincare.Analysis.MatrixGinibreSpectralLaw
public import GinibrePoincare.Analysis.MatrixSymmetrizedSpectralLaw
public import GinibrePoincare.Analysis.PermutationLp

@[expose] public section

open Matrix MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

def matrixSpectralPermutationAverage (n : ℕ) (F : (Fin n → ℂ) → ℝ≥0∞)
    (z : Fin n → ℂ) : ℝ≥0∞ :=
  (Fintype.card (Fin n ≃ Fin n) : ℝ≥0∞)⁻¹ * ∑ e : Fin n ≃ Fin n, F (z ∘ e)

theorem matrixSpectralPermutationAverage_measurable {n : ℕ}
    (F : (Fin n → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    Measurable (matrixSpectralPermutationAverage n F) := by
  classical
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro e he
  exact hF.comp (by fun_prop)

theorem matrixSpectralPermutationAverage_symmetric {n : ℕ}
    (F : (Fin n → ℂ) → ℝ≥0∞) (p : Fin n ≃ Fin n) (z : Fin n → ℂ) :
    matrixSpectralPermutationAverage n F (z ∘ p) = matrixSpectralPermutationAverage n F z := by
  classical
  unfold matrixSpectralPermutationAverage
  congr 1
  have h := Equiv.sum_comp (Equiv.mulLeft p) (fun e : Fin n ≃ Fin n => F (z ∘ e))
  change (∑ e : Fin n ≃ Fin n, F (z ∘ (p * e : Equiv.Perm (Fin n)))) = (∑ e : Fin n ≃ Fin n, F (z ∘ e)) at h
  simpa only [Function.comp_def, Equiv.Perm.mul_apply] using h

theorem matrixSpectralPermutationAverage_lintegral {n : ℕ}
    (μ : Measure (Fin n → ℂ))
    (hμ : ∀ e : Fin n ≃ Fin n, μ.map (fun z => z ∘ e) = μ)
    (F : (Fin n → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ z, matrixSpectralPermutationAverage n F z ∂μ = ∫⁻ z, F z ∂μ := by
  classical
  have hm : ∀ e : Fin n ≃ Fin n, Measurable (fun z : Fin n → ℂ => F (z ∘ e)) :=
    fun _ => hF.comp (by fun_prop)
  have hs : Measurable (fun z : Fin n → ℂ => ∑ e : Fin n ≃ Fin n, F (z ∘ e)) :=
    Finset.measurable_sum _ (fun e _ => hm e)
  unfold matrixSpectralPermutationAverage
  rw [lintegral_const_mul _ hs, lintegral_finsetSum Finset.univ (fun e _ => hm e)]
  have hi : ∀ e : Fin n ≃ Fin n, (∫⁻ z, F (z ∘ e) ∂μ) = ∫⁻ z, F z ∂μ := by
    intro e
    rw [← lintegral_map hF (by fun_prop), hμ e]
  simp_rw [hi]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, ENNReal.inv_mul_cancel
    (by exact_mod_cast Fintype.card_ne_zero : (Fintype.card (Fin n ≃ Fin n) : ℝ≥0∞) ≠ 0)
    (ENNReal.natCast_ne_top _), one_mul]

/-- Uniform random relabeling of the actual Gaussian matrix spectrum has exactly
normalized Ginibre law, for arbitrary measurable tests. -/
theorem matrixSymmetrizedSpectralMeasure_eq_ginibre {n : ℕ} (hn : 0 < n) :
    matrixSymmetrizedSpectralMeasure n = ginibreMeasure n := by
  apply Measure.ext_of_lintegral
  intro F hF
  let A := matrixSpectralPermutationAverage n F
  have hA : Measurable A := matrixSpectralPermutationAverage_measurable F hF
  have hsym : ∀ e : Fin n ≃ Fin n, ∀ z, A (z ∘ e) = A z :=
    matrixSpectralPermutationAverage_symmetric F
  have he : (∫⁻ z, A z ∂matrixSymmetrizedSpectralMeasure n) = ∫⁻ z, A z ∂ginibreMeasure n := by
    rw [matrixSymmetrizedSpectralMeasure_lintegral_symmetric n A hA hsym,
      matrixSpectralMeasure, lintegral_map hA (matrixMeasurableEigenvalues_measurable n)]
    exact matrixGaussian_symmetric_spectral_lintegral hn A hA hsym
  have hm : ∀ e : Fin n ≃ Fin n,
      (matrixSymmetrizedSpectralMeasure n).map (fun z => z ∘ e) = matrixSymmetrizedSpectralMeasure n :=
    matrixSymmetrizedSpectralMeasure_relabel n
  have hg : ∀ e : Fin n ≃ Fin n, (ginibreMeasure n).map (fun z => z ∘ e) = ginibreMeasure n :=
    fun e => (ginibre_measurePreserving_permute e).map_eq
  rw [matrixSpectralPermutationAverage_lintegral _ hm F hF,
    matrixSpectralPermutationAverage_lintegral _ hg F hF] at he
  exact he

#print axioms matrixSymmetrizedSpectralMeasure_eq_ginibre
end
end GinibrePoincare
