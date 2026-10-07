module

public import GinibrePoincare.Analysis.MatrixLocalEigenvalue
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

@[expose] public section

/-! # Jacobi's differential formula without an invertibility assumption -/
open scoped BigOperators Topology
open Matrix
namespace GinibrePoincare
noncomputable section

def matrixDeterminantMultilinear (n : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin n => Fin n → ℂ) ℂ where
  toMultilinearMap := (Matrix.detRowAlternating (n := Fin n) (R := ℂ)).toMultilinearMap
  cont := by
    change Continuous (fun G : GinibreMatrixCoordinates n => (Matrix.of G).det)
    simp only [Matrix.det_apply', Matrix.of_apply]
    fun_prop

theorem matrixDeterminantMultilinear_apply (n : ℕ) (G : GinibreMatrixCoordinates n) :
    matrixDeterminantMultilinear n G = (Matrix.of G).det := rfl

def matrixDeterminantDerivative (n : ℕ) (G : GinibreMatrixCoordinates n) :
    GinibreMatrixCoordinates n →L[ℂ] ℂ :=
  (matrixDeterminantMultilinear n).linearDeriv G

theorem matrixDeterminant_hasFDerivAt (n : ℕ) (G : GinibreMatrixCoordinates n) :
    HasFDerivAt (fun A : GinibreMatrixCoordinates n => (Matrix.of A).det)
      (matrixDeterminantDerivative n G) G :=
  (matrixDeterminantMultilinear n).hasFDerivAt G

theorem matrixDeterminantDerivative_apply (n : ℕ) (G H : GinibreMatrixCoordinates n) :
    matrixDeterminantDerivative n G H =
      Matrix.trace ((Matrix.of G).adjugate * Matrix.of H) := by
  rw [matrixDeterminantDerivative, ContinuousMultilinearMap.linearDeriv_apply]
  simp only [matrixDeterminantMultilinear_apply]
  have hrow (i : Fin n) : (Matrix.of (Function.update G i (H i))).det =
      ∑ j, (Matrix.of G).adjugate j i * H i j := by
    change ((Matrix.of G).updateRow i (H i)).det = _
    rw [← Matrix.cramer_transpose_apply, Matrix.cramer_eq_adjugate_mulVec,
      ← Matrix.adjugate_transpose]
    simp [Matrix.mulVec, dotProduct]
  simp_rw [hrow]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.sum_comm]

#print axioms matrixDeterminant_hasFDerivAt
#print axioms matrixDeterminantDerivative_apply

end
end GinibrePoincare
