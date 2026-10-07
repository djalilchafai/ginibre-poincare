module

public import GinibrePoincare.Analysis.MatrixSchurJacobian
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential

@[expose] public section

open Matrix NormedSpace
open scoped Matrix Matrix.Norms.Operator
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def schurAmbientChart {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (p : Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := exp p.1 * (T + p.2) * exp (-p.1)

theorem schurAmbientChart_fderiv {n : ℕ} (T K H : Matrix (Fin n) (Fin n) ℂ) :
    fderiv ℝ (schurAmbientChart T) (0, 0) (K, H) = K * T - T * K + H := by
  let M := Matrix (Fin n) (Fin n) ℂ
  have hfst : HasFDerivAt (Prod.fst : M × M → M) (ContinuousLinearMap.fst ℝ M M) (0, 0) := hasFDerivAt_fst
  have hsnd : HasFDerivAt (Prod.snd : M × M → M) (ContinuousLinearMap.snd ℝ M M) (0, 0) := hasFDerivAt_snd
  have hexp : HasFDerivAt (exp : M → M) (1 : M →L[ℝ] M) 0 := hasFDerivAt_exp_zero
  have hL := hexp.comp ((0, 0) : M × M) hfst
  have hx : (-Prod.fst) ((0, 0) : M × M) = 0 := by simp
  rw [← hx] at hexp
  have hR := hexp.comp ((0, 0) : M × M) hfst.neg
  have hM := (hasFDerivAt_const T ((0, 0) : M × M)).add hsnd
  have hd := (hL.mul' hM).mul' hR
  unfold schurAmbientChart
  have he := congrArg (fun L : M × M →L[ℝ] M => L (K, H)) hd.fderiv
  simpa [exp_zero, ContinuousLinearMap.comp_apply, mul_add, add_mul, sub_eq_add_neg,
    add_assoc, add_comm, add_left_comm, Function.comp_def, Pi.mul_def, Pi.add_def, Pi.neg_def] using he

#print axioms schurAmbientChart_fderiv

theorem schurAmbientChart_skew_unitary {n : ℕ} (T H : Matrix (Fin n) (Fin n) ℂ)
    (x : SchurLowerIndex n → ℂ) :
    exp (schurSkewCombination x) ∈ Matrix.unitaryGroup (Fin n) ℂ ∧
      schurAmbientChart T (schurSkewCombination x, H) =
        exp (schurSkewCombination x) * (T + H) * (exp (schurSkewCombination x))ᴴ := by
  have hskew : schurSkewCombination x ∈ skewAdjoint (Matrix (Fin n) (Fin n) ℂ) :=
    skewAdjoint.mem_iff.mpr (schurSkewCombination_conjTranspose x)
  refine ⟨exp_mem_unitary_of_mem_skewAdjoint hskew, ?_⟩
  unfold schurAmbientChart
  rw [← Matrix.exp_conjTranspose, schurSkewCombination_conjTranspose]

/-- The previously computed Vandermonde block occurs in the actual real chart derivative
for skew-Hermitian lower coordinates and upper-triangular perturbations. -/
theorem schurAmbientChart_fderiv_lowerBlock {n : ℕ} (T H : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0) (hH : ∀ i j, j < i → H i j = 0)
    (x : SchurLowerIndex n → ℂ) (p : SchurLowerIndex n) :
    fderiv ℝ (schurAmbientChart T) (0, 0) (schurSkewCombination x, H)
      (schurLowerRow p) (schurLowerCol p) = (schurLowerJacobian T *ᵥ x) p := by
  rw [schurAmbientChart_fderiv, Matrix.add_apply]
  have hz : H (schurLowerRow p) (schurLowerCol p) = 0 := hH _ _ p.property
  rw [hz, add_zero]
  exact (schurLowerJacobian_skew_commutator T hT x p).symm

#print axioms schurAmbientChart_fderiv_lowerBlock
end
end GinibrePoincare
