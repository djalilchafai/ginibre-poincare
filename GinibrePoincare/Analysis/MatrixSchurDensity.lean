module

public import GinibrePoincare.Analysis.MatrixGaussianMeasure
public import Mathlib.LinearAlgebra.UnitaryGroup

@[expose] public section

open Matrix
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

theorem matrixHSNormSq_unitary_conjugation (n : ℕ) (A U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    matrixHSNormSq (U * A * Uᴴ) = matrixHSNormSq A := by
  have h2 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hp : (U * A * Uᴴ) * (U * A * Uᴴ)ᴴ = U * (A * Aᴴ) * Uᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = U * A * (Uᴴ * U) * Aᴴ * Uᴴ := by noncomm_ring
      _ = U * (A * Aᴴ) * Uᴴ := by rw [h2]; simp [Matrix.mul_assoc]
  unfold matrixHSNormSq
  rw [hp, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem matrixHSNormSq_diag_remainder (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    matrixHSNormSq A = (∑ i, Complex.normSq (A i i)) +
      matrixHSNormSq (A - Matrix.diagonal fun i => A i i) := by
  classical
  simp_rw [matrixHSNormSq_eq_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hd : Complex.normSq (A i i) =
      ∑ j : Fin n, if i = j then Complex.normSq (A i j) else 0 := by simp
  rw [hd, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i = j
  · subst j; simp
  · simp [Matrix.diagonal_apply, hij]

/-- The Gaussian matrix density in unitary Schur coordinates factors into a diagonal
Gaussian term and an independent off-diagonal Gaussian term. -/
theorem matrixGaussianDensity_unitary_schur (n : ℕ) (T U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    matrixGaussianDensity n (U * T * Uᴴ) =
      ENNReal.ofReal (((n : ℝ) / Real.pi) ^ (n * n) *
        Real.exp (-(n : ℝ) * ∑ i, Complex.normSq (T i i)) *
        Real.exp (-(n : ℝ) * matrixHSNormSq (T - Matrix.diagonal fun i => T i i))) := by
  rw [matrixGaussianDensity, matrixHSNormSq_unitary_conjugation n T U hU,
    matrixHSNormSq_diag_remainder]
  rw [mul_add, Real.exp_add]
  congr 1
  ring

#print axioms matrixGaussianDensity_unitary_schur
end
end GinibrePoincare
