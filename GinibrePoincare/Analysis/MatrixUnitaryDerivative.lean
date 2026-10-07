module

public import GinibrePoincare.Analysis.MatrixSkewCoordinates
public import Mathlib.Analysis.Calculus.FDeriv.Mul

@[expose] public section

open Matrix Filter
open scoped Matrix Matrix.Norms.Operator Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Differentiating actual unitary paths yields a skew-Hermitian left logarithmic derivative. -/
theorem matrixUnitary_left_derivative_skew {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} {Q : E → Matrix (Fin n) (Fin n) ℂ} {D : E →L[ℝ] Matrix (Fin n) (Fin n) ℂ}
    {x : E} (hQ : HasFDerivAt Q D x)
    (hunit : ∀ᶠ y in 𝓝 x, Q y ∈ Matrix.unitaryGroup (Fin n) ℂ) (v : E) :
    ((Q x)ᴴ * D v)ᴴ = -((Q x)ᴴ * D v) := by
  let A := schurConjTransposeCLM n
  have hs := A.hasFDerivAt.comp x hQ
  have hp := hs.mul' hQ
  have hevent : (fun y => A (Q y) * Q y) =ᶠ[𝓝 x] (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ)) := by
    filter_upwards [hunit] with y hy
    exact Matrix.mem_unitaryGroup_iff'.mp hy
  have hc := (hasFDerivAt_const (𝕜 := ℝ) (1 : Matrix (Fin n) (Fin n) ℂ) x).congr_of_eventuallyEq hevent
  have he := hp.unique hc
  have hv := congrArg (fun L : E →L[ℝ] Matrix (Fin n) (Fin n) ℂ => L v) he
  have hz : (Q x)ᴴ * D v + (D v)ᴴ * Q x = 0 := by
    simpa [A, schurConjTransposeCLM, ContinuousLinearMap.comp_apply] using hv
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  exact eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hz)

#print axioms matrixUnitary_left_derivative_skew
end
end GinibrePoincare
