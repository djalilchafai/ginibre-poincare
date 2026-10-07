module

public import GinibrePoincare.Analysis.MatrixGaussianMeasure

@[expose] public section

/-! # Actual strictly positive bounded Gaussian matrix density -/
open MeasureTheory Matrix
open scoped ENNReal
namespace GinibrePoincare
noncomputable section

def matrixGaussianDensityReal (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (((n : ℝ) / Real.pi) ^ (n * n)) * Real.exp (-(n : ℝ) * matrixHSNormSq A)

theorem matrixGaussianDensityReal_pos (n : ℕ) (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℂ) : 0 < matrixGaussianDensityReal n A := by
  unfold matrixGaussianDensityReal
  positivity

theorem matrixGaussianDensity_le_const (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    matrixGaussianDensity n A ≤ ENNReal.ofReal (((n : ℝ) / Real.pi) ^ (n * n)) := by
  apply ENNReal.ofReal_le_ofReal
  have he : Real.exp (-(n : ℝ) * matrixHSNormSq A) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n))
      (matrixHSNormSq_nonneg A)
  change (((n : ℝ) / Real.pi) ^ (n * n)) * Real.exp (-(n : ℝ) * matrixHSNormSq A) ≤ _
  exact (mul_le_mul_of_nonneg_left he (by positivity)).trans_eq (mul_one _)

theorem matrixGaussianMeasure_le_finite_smul_volume (n : ℕ) (hn : 0 < n) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧
      matrixGaussianMeasure n ≤ c • (volume : Measure (Matrix (Fin n) (Fin n) ℂ)) := by
  refine ⟨ENNReal.ofReal (((n : ℝ) / Real.pi) ^ (n * n)), ENNReal.ofReal_ne_top, ?_⟩
  rw [matrixGaussianMeasure_eq_withDensity hn, ← withDensity_const]
  exact withDensity_mono (Filter.Eventually.of_forall (matrixGaussianDensity_le_const n))

end
end GinibrePoincare
