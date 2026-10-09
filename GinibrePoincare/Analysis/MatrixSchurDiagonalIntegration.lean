module

public import GinibrePoincare.Analysis.MatrixSchurUpperGaussian

@[expose] public section

open Matrix MeasureTheory Set
open scoped Matrix Matrix.Norms.Operator ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

def schurDiagonalSpectralDensity (n : ℕ) (z : Fin n → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (vandermondeWeight z) *
    ENNReal.ofReal (Real.exp (-(n : ℝ) * ∑ i, Complex.normSq (z i)))

theorem measurable_schurDiagonalSpectralDensity (n : ℕ) :
    Measurable (schurDiagonalSpectralDensity n) := by
  have hv : Measurable (fun z : Fin n → ℂ => vandermondeWeight z) :=
    Complex.continuous_normSq.measurable.comp continuous_vandermonde.measurable
  unfold schurDiagonalSpectralDensity
  apply Measurable.mul (ENNReal.measurable_ofReal.comp hv)
  fun_prop

/-- The independent strict upper Gaussian integrates to one in the actual Schur
formula, leaving exactly the ordered eigenvalue Vandermonde-Gaussian density. -/
theorem matrixSchur_sortedUpper_diagonal_integral {n : ℕ} (hn : 0 < n)
    (F : (Fin n → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ y in matrixSchurSortedUpperDomain n,
      ENNReal.ofReal (vandermondeWeight (fun i => schurUpperCombination y i i)) *
        (matrixGaussianDensity n (schurUpperCombination y) * F (fun i => schurUpperCombination y i i)) =
      schurUpperGaussianDiagonalFactor n *
        ∫⁻ z in matrixSchurOrderedConfigurations n, schurDiagonalSpectralDensity n z * F z := by
  have hd : ∀ y : SchurUpperIndex n → ℂ,
      (fun i => schurUpperCombination y i i) = (schurUpperSplit n y).1 := by
    intro y
    funext i
    exact schurUpperCombination_entry y ⟨(i, i), le_refl i⟩
  have hm : Measurable (fun u : SchurStrictUpperIndex n → ℂ => schurStrictUpperGaussianDensity n u) := by
    unfold schurStrictUpperGaussianDensity
    apply Finset.measurable_prod
    intro i hi
    exact (measurable_complexCoordinateGaussianDensity n).comp (measurable_pi_apply i)
  have hf := (measurable_schurDiagonalSpectralDensity n).mul hF
  have hsplit := schurUpperSplit_sorted_lintegral
    (fun z => schurDiagonalSpectralDensity n z * F z) hf
    (schurStrictUpperGaussianDensity n) hm
  have he : (fun y : SchurUpperIndex n → ℂ =>
      ENNReal.ofReal (vandermondeWeight (fun i => schurUpperCombination y i i)) *
        (matrixGaussianDensity n (schurUpperCombination y) * F (fun i => schurUpperCombination y i i))) =
      (fun y => schurUpperGaussianDiagonalFactor n *
        ((schurDiagonalSpectralDensity n (schurUpperSplit n y).1 * F (schurUpperSplit n y).1) *
          schurStrictUpperGaussianDensity n (schurUpperSplit n y).2)) := by
    funext y
    rw [matrixGaussianDensity_schurUpper_normalized_split hn, hd]
    unfold schurDiagonalSpectralDensity
    ac_rfl
  rw [he, lintegral_const_mul _]
  · rw [hsplit, schurStrictUpperGaussianDensity_integral hn, mul_one]
  · exact (hf.comp ((schurUpperSplit_volume_preserving n).measurable.fst)).mul
      (hm.comp ((schurUpperSplit_volume_preserving n).measurable.snd))

#print axioms matrixSchur_sortedUpper_diagonal_integral
end
end GinibrePoincare
