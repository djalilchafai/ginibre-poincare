module

public import GinibrePoincare.Analysis.MatrixSchurFrameJacobian
public import Mathlib.Analysis.Calculus.ContDiff.Defs

@[expose] public section

open Matrix NormedSpace Filter
open scoped Matrix Matrix.Norms.Operator Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

/-- The actual lower skew exponential section of the unitary group. -/
def matrixSchurExponentialFrame (n : ℕ) (x : SchurLowerIndex n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ := exp (schurSkewCombination x)

theorem matrixSchurExponentialFrame_unitary (n : ℕ) (x : SchurLowerIndex n → ℂ) :
    matrixSchurExponentialFrame n x ∈ Matrix.unitaryGroup (Fin n) ℂ :=
  (schurAmbientChart_skew_unitary (0 : Matrix (Fin n) (Fin n) ℂ) 0 x).1

theorem matrixSchurExponentialFrame_differentiable (n : ℕ) :
    Differentiable ℝ (matrixSchurExponentialFrame n) := by
  intro x
  have he := (exp_analytic (𝕂 := ℝ) (schurSkewCombination x)).differentiableAt
  have hs := (schurSkewCLM n).differentiableAt (x := x)
  rw [← schurSkewCLM_apply] at he
  have hf : matrixSchurExponentialFrame n = exp ∘ ⇑(schurSkewCLM n) := by
    funext z
    rw [Function.comp_apply, schurSkewCLM_apply]
    rfl
  rw [hf]
  exact he.comp x hs

/-- The angular density is defined from the derivative of the actual unitary section,
independently of all eigenvalues and strict upper entries. -/
def matrixSchurAngularDensity (n : ℕ) (x : SchurLowerIndex n → ℂ) : ℝ :=
  |(((matrixLowerRead n).comp (matrixUnitaryConnection (matrixSchurExponentialFrame n x)
    (fderiv ℝ (matrixSchurExponentialFrame n) x))).toLinearMap).det|

theorem matrixSchurAngularDensity_nonneg (n : ℕ) (x : SchurLowerIndex n → ℂ) :
    0 ≤ matrixSchurAngularDensity n x := abs_nonneg _

/-- The Schur Jacobian factorization for the concrete exponential chart at every point. -/
theorem matrixSchurExponentialJacobian {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : ∀ i j, j < i → T i j = 0)
    (x : SchurLowerIndex n → ℂ) (y : SchurUpperIndex n → ℂ) :
    |(schurEntryCoordinates.comp
        (fderiv ℝ (matrixSchurFrameChart (matrixSchurExponentialFrame n) T) (x, y)).toLinearMap).det| =
      vandermondeWeight (fun i => (T + schurUpperCombination y) i i) *
        matrixSchurAngularDensity n x := by
  apply matrixSchurFrame_entry_fderiv_abs_det
  · exact hT
  · exact (matrixSchurExponentialFrame_differentiable n x).hasFDerivAt
  · exact Filter.Eventually.of_forall (matrixSchurExponentialFrame_unitary n)

#print axioms matrixSchurExponentialJacobian
end
end GinibrePoincare
