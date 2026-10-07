module

public import GinibrePoincare.Analysis.MatrixSpectralSobolevCoordinates

@[expose] public section

/-! # Exact real gradient directions under matrix entry reindexing -/
open Matrix
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def matrixEntryRealIndexEquiv {n m : ℕ} (e : Fin m ≃ Fin n × Fin n) :
    (Fin m × Fin 2) ≃ MatrixRealIndex n where
  toFun p := ⟨(e p.1).1, ⟨(e p.1).2, p.2⟩⟩
  invFun i := (e.symm (i.1, i.2.1), i.2.2)
  left_inv p := by simp
  right_inv i := by cases i with | mk i q => cases q with | mk j k => simp

theorem matrixComplexEntryEquiv_direction {n m : ℕ} (e : Fin m ≃ Fin n × Fin n)
    (p : Fin m × Fin 2) :
    matrixComplexEntryEquiv e (ginibreCoordinateDirection p) =
      matrixRealCoordinates n (Pi.single (matrixEntryRealIndexEquiv e p) 1) := by
  classical
  rw [matrixEntryRealIndexEquiv, matrixRealCoordinates_direction]
  funext i j
  have he (a b : Fin n) : e.symm (a, b) = p.1 ↔ a = (e p.1).1 ∧ b = (e p.1).2 := by
    rw [Equiv.symm_apply_eq, Prod.ext_iff]
  by_cases hp : p.2 = 0 <;>
    by_cases hi : i = (e p.1).1 <;> by_cases hj : j = (e p.1).2 <;>
    simp [matrixComplexEntryEquiv, ginibreCoordinateDirection, realCoordinateDirection,
      imaginaryCoordinateDirection, coordinateDirection, Pi.single_apply, hp, hi, hj, he]

end
end GinibrePoincare
