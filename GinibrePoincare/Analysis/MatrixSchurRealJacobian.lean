module

public import GinibrePoincare.Analysis.MatrixSchurJacobian
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Complex

@[expose] public section

open Matrix
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The real Jacobian determinant of the complex lower Schur block. -/
theorem schurLowerJacobian_real_det {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0) :
    ((Matrix.toLin' (schurLowerJacobian T)).restrictScalars ℝ).det =
      vandermondeWeight (fun i => T i i) := by
  rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_eq]
  exact schurLowerJacobian_normSq_det T hT

#print axioms schurLowerJacobian_real_det
end
end GinibrePoincare
