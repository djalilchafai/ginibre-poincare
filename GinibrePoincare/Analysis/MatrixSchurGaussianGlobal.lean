module

public import GinibrePoincare.Analysis.MatrixSchurGlobalIntegration

@[expose] public section

/-! # Inserting the Gaussian density into global Schur integration

The matrix Gaussian density depends only on the Hilbert–Schmidt squared norm,
which is invariant under unitary conjugation. Multiply a unitary-invariant test
by that density and apply the global volume integration formula. Testing with
the constant one gives the mass equation that determines the common angular
constant in subsequent spectral-law comparisons.
-/


open Matrix NormedSpace MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator Topology ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem matrixGaussianDensity_unitary_invariant (n : ℕ)
    (U A : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    matrixGaussianDensity n (U * A * Uᴴ) = matrixGaussianDensity n A := by
  unfold matrixGaussianDensity
  rw [matrixHSNormSq_unitary_conjugation n A U hU]

/-- The genuine Gaussian matrix integral is a single angular constant times the
sorted triangular Vandermonde integral, and its total mass fixes that constant. -/
theorem matrixSchur_gaussian_global_integral {n : ℕ} (hn : 0 < n) :
    ∃ c : ℝ≥0∞,
      (∀ g : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞, Measurable g →
        (∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ A, g (U * A * Uᴴ) = g A) →
        ∫⁻ A, g A ∂matrixGaussianMeasure n = c *
          ∫⁻ y in matrixSchurSortedUpperDomain n,
            ENNReal.ofReal (vandermondeWeight (fun i => schurUpperCombination y i i)) *
              (matrixGaussianDensity n (schurUpperCombination y) * g (schurUpperCombination y))) ∧
      1 = c * ∫⁻ y in matrixSchurSortedUpperDomain n,
        ENNReal.ofReal (vandermondeWeight (fun i => schurUpperCombination y i i)) *
          matrixGaussianDensity n (schurUpperCombination y) := by
  obtain ⟨c, hc⟩ := matrixSchur_global_integral n
  have h : ∀ g : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞, Measurable g →
      (∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ A, g (U * A * Uᴴ) = g A) →
      ∫⁻ A, g A ∂matrixGaussianMeasure n = c *
        ∫⁻ y in matrixSchurSortedUpperDomain n,
          ENNReal.ofReal (vandermondeWeight (fun i => schurUpperCombination y i i)) *
            (matrixGaussianDensity n (schurUpperCombination y) * g (schurUpperCombination y)) := by
    intro g hg hInv
    rw [matrixGaussianMeasure_eq_withDensity hn,
      lintegral_withDensity_eq_lintegral_mul volume (measurable_matrixGaussianDensity n) hg]
    apply hc
    · exact (measurable_matrixGaussianDensity n).mul hg
    · intro U hU A
      simp only [Pi.mul_apply]
      rw [matrixGaussianDensity_unitary_invariant n U A hU, hInv U hU A]
  refine ⟨c, h, ?_⟩
  have h1 := h (fun _ => 1) measurable_const (by intros; rfl)
  simpa only [mul_one, lintegral_const, measure_univ, one_mul] using h1

#print axioms matrixSchur_gaussian_global_integral
end
end GinibrePoincare
