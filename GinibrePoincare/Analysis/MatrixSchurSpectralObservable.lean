module

public import GinibrePoincare.Analysis.MatrixSymmetricLift
public import GinibrePoincare.Analysis.MatrixSchurDensity

@[expose] public section

open Matrix
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem matrix_charpoly_unitary_conjugation {n : ℕ} (T U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (U * T * Uᴴ).charpoly = T.charpoly := by
  have hh : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hh]
  simp

theorem schur_diagonal_roots {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0) (i : Fin n) : T.charpoly.eval (T i i) = 0 := by
  classical
  rw [Matrix.charpoly_of_isUpperTriangular T hT, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

/-- A symmetric spectral observable is exactly the same function of the Schur diagonal,
independently of the unitary conjugating matrix and the strict upper entries. -/
theorem matrixSymmetricLift_unitary_schur {n : ℕ} (T U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0) (hd : Function.Injective (fun i => T i i))
    (F : (Fin n → ℂ) → ℝ) (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) :
    matrixSymmetricLift n F (U * T * Uᴴ) = F (fun i => T i i) := by
  have hr : ∀ i, (U * T * Uᴴ).charpoly.eval (T i i) = 0 := by
    intro i
    rw [matrix_charpoly_unitary_conjugation T U hU]
    exact schur_diagonal_roots T hT i
  have hs := matrix_injective_full_roots_separable n (U * T * Uᴴ) _ hd hr
  have hc := matrixMeasurableEigenvalues_spec n (U * T * Uᴴ) hs
  exact matrixSimpleSpectrum_symmetric_value n (U * T * Uᴴ) hs
    (matrixMeasurableEigenvalues n (U * T * Uᴴ)) (fun i => T i i)
    hc.1 hd hc.2 hr F hsym

#print axioms matrixSymmetricLift_unitary_schur
end
end GinibrePoincare
