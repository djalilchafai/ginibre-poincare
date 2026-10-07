module

public import GinibrePoincare.Analysis.MatrixUnitaryFlagSlice
public import GinibrePoincare.Analysis.MatrixSchurUniqueness

@[expose] public section

open Matrix NormedSpace Filter Set
open scoped Matrix Matrix.Norms.Operator Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

/-- One unitary-coordinate neighborhood works for all triangular matrices and all
strict upper entries. This is stronger than an inverse-function neighborhood of one matrix. -/
theorem matrixSchur_uniform_ordered_slice (n : ℕ) :
    ∃ V : Set (SchurLowerIndex n → ℂ), V ∈ 𝓝 0 ∧
      ∀ x ∈ V, ∀ y ∈ V, ∀ A B : Matrix (Fin n) (Fin n) ℂ,
        (∀ i j, j < i → A i j = 0) → (∀ i j, j < i → B i j = 0) →
        (∀ i, A i i = B i i) → Function.Injective (fun i => A i i) →
        matrixSchurExponentialFrame n x * A * (matrixSchurExponentialFrame n x)ᴴ =
          matrixSchurExponentialFrame n y * B * (matrixSchurExponentialFrame n y)ᴴ →
        x = y ∧ A = B := by
  obtain ⟨V, hV, hflag⟩ := matrixUnitary_lower_flag_slice n
  refine ⟨V, hV, ?_⟩
  intro x hx y hy A B hA hB hd hinj he
  let Q := matrixSchurExponentialFrame n
  have hphase := schur_ordered_representation_unique_phases
    (Q x * A * (Q x)ᴴ) A B (Q x) (Q y)
    (matrixSchurExponentialFrame_unitary n x) (matrixSchurExponentialFrame_unitary n y)
    hA hB hd hinj rfl he
  have hxy : x = y := hflag x hx y hy (by
    intro i j hij
    rw [hphase]
    simp [Matrix.diagonal_apply, hij])
  refine ⟨hxy, ?_⟩
  rw [← hxy] at he
  have h1 : (Q x)ᴴ * Q x = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (matrixSchurExponentialFrame_unitary n x)
  have hc : ∀ M : Matrix (Fin n) (Fin n) ℂ,
      (Q x)ᴴ * (Q x * M * (Q x)ᴴ) * Q x = M := by
    intro M
    calc
      _ = ((Q x)ᴴ * Q x) * M * ((Q x)ᴴ * Q x) := by noncomm_ring
      _ = M := by rw [h1]; simp
  have hm := congrArg (fun M => (Q x)ᴴ * M * Q x) he
  rw [hc, hc] at hm
  exact hm

#print axioms matrixSchur_uniform_ordered_slice
end
end GinibrePoincare
