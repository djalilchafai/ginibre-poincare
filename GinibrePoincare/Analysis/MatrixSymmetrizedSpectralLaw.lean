module

public import GinibrePoincare.Analysis.MatrixSpectralLaw

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
namespace GinibrePoincare
noncomputable section

def spectralRelabel (n : ℕ) (e : Equiv.Perm (Fin n)) (z : Fin n → ℂ) : Fin n → ℂ := z ∘ e

theorem spectralRelabel_measurable (n : ℕ) (e : Equiv.Perm (Fin n)) :
    Measurable (spectralRelabel n e) := Measurable.of_eval fun i => measurable_pi_apply (e i)

/-- Uniform randomization of all label permutations of the actual matrix spectral law. -/
def matrixSymmetrizedSpectralMeasure (n : ℕ) : Measure (Fin n → ℂ) :=
  (Fintype.card (Equiv.Perm (Fin n)) : ℝ≥0∞)⁻¹ •
    ∑ e : Equiv.Perm (Fin n), (matrixSpectralMeasure n).map (spectralRelabel n e)

instance matrixSymmetrizedSpectralMeasure_isProbability (n : ℕ) :
    IsProbabilityMeasure (matrixSymmetrizedSpectralMeasure n) := by
  constructor
  rw [matrixSymmetrizedSpectralMeasure, Measure.smul_apply,
    Measure.finsetSum_apply]
  simp only [Measure.map_apply (spectralRelabel_measurable n _) MeasurableSet.univ,
    Set.preimage_univ, measure_univ, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero)
    (ENNReal.natCast_ne_top _)

/-- The randomized spectral law is exchangeable under every permutation. -/
theorem matrixSymmetrizedSpectralMeasure_relabel (n : ℕ) (e : Equiv.Perm (Fin n)) :
    (matrixSymmetrizedSpectralMeasure n).map (spectralRelabel n e) =
      matrixSymmetrizedSpectralMeasure n := by
  ext s hs
  rw [Measure.map_apply (spectralRelabel_measurable n e) hs]
  simp only [matrixSymmetrizedSpectralMeasure, Measure.smul_apply,
    Measure.finsetSum_apply, smul_eq_mul]
  congr 1
  simp only [Measure.map_apply (spectralRelabel_measurable n _) hs,
    Measure.map_apply (spectralRelabel_measurable n _) ((spectralRelabel_measurable n e) hs)]
  have he (d : Equiv.Perm (Fin n)) :
      spectralRelabel n d ⁻¹' (spectralRelabel n e ⁻¹' s) =
        spectralRelabel n (d * e) ⁻¹' s := by
    ext z
    rfl
  simp_rw [he]
  exact Equiv.sum_comp (Equiv.mulRight e)
    (fun d => matrixSpectralMeasure n (spectralRelabel n d ⁻¹' s))

#print axioms matrixSymmetrizedSpectralMeasure_relabel

/-- Uniform random labels preserve every symmetric nonnegative spectral expectation. -/
theorem matrixSymmetrizedSpectralMeasure_lintegral_symmetric (n : ℕ)
    (F : (Fin n → ℂ) → ℝ≥0∞) (hF : Measurable F)
    (hsym : ∀ e : Equiv.Perm (Fin n), ∀ z, F (z ∘ e) = F z) :
    (∫⁻ z, F z ∂matrixSymmetrizedSpectralMeasure n) =
      ∫⁻ z, F z ∂matrixSpectralMeasure n := by
  rw [matrixSymmetrizedSpectralMeasure, lintegral_smul_measure, lintegral_finsetSum_measure]
  have he (e : Equiv.Perm (Fin n)) :
      (∫⁻ z, F z ∂(matrixSpectralMeasure n).map (spectralRelabel n e)) =
        ∫⁻ z, F z ∂matrixSpectralMeasure n := by
    rw [lintegral_map hF (spectralRelabel_measurable n e)]
    apply lintegral_congr
    intro z
    exact hsym e z
  simp_rw [he]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul]
  rw [← mul_assoc, ENNReal.inv_mul_cancel
    (by exact_mod_cast Fintype.card_ne_zero :
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ≥0∞) ≠ 0) (ENNReal.natCast_ne_top _), one_mul]

#print axioms matrixSymmetrizedSpectralMeasure_lintegral_symmetric
end
end GinibrePoincare
