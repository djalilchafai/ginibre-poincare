module

public import GinibrePoincare.Analysis.MatrixSchurAngularChart
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Algebra.Star.Unitary

@[expose] public section

open Matrix NormedSpace Filter Set
open scoped Matrix Matrix.Norms.Operator Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

/-- Every unitary flag is covered by a countable family of translated copies of the
actual phase-saturated angular chart. -/
theorem matrixUnitaryFlagSaturation_countable_cover (n : ℕ)
    (V : Set (SchurLowerIndex n → ℂ)) (h0 : 0 ∈ V)
    (hopen : IsOpen {U : Matrix.unitaryGroup (Fin n) ℂ |
      (U : Matrix (Fin n) (Fin n) ℂ) ∈ matrixUnitaryFlagSaturation n V}) :
    ∃ C : ℕ → Matrix.unitaryGroup (Fin n) ℂ,
      ∀ U : Matrix.unitaryGroup (Fin n) ℂ, ∃ k,
        ((C k : Matrix (Fin n) (Fin n) ℂ)ᴴ * (U : Matrix (Fin n) (Fin n) ℂ)) ∈
          matrixUnitaryFlagSaturation n V := by
  let H := Matrix.unitaryGroup (Fin n) ℂ
  let S : Set H := {U | (U : Matrix (Fin n) (Fin n) ℂ) ∈ matrixUnitaryFlagSaturation n V}
  let O : H → Set H := fun C => (fun U : H => star C * U) ⁻¹' S
  have hO : ∀ C, IsOpen (O C) := fun C => hopen.preimage (continuous_const.mul continuous_id)
  have hcover : (Set.univ : Set H) ⊆ ⋃ C, O C := by
    intro U hU
    apply Set.mem_iUnion.mpr
    refine ⟨U, ?_⟩
    change ((U : Matrix (Fin n) (Fin n) ℂ)ᴴ * (U : Matrix (Fin n) (Fin n) ℂ)) ∈
      matrixUnitaryFlagSaturation n V
    rw [show (U : Matrix (Fin n) (Fin n) ℂ)ᴴ * (U : Matrix (Fin n) (Fin n) ℂ) = 1 from
      Matrix.mem_unitaryGroup_iff'.mp U.property]
    exact matrixUnitaryFlagSaturation_one V h0
  obtain ⟨C, hC⟩ := isLindelof_univ.indexed_countable_subcover O hO hcover
  refine ⟨C, fun U => ?_⟩
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp (hC (Set.mem_univ U))
  exact ⟨k, hk⟩

#print axioms matrixUnitaryFlagSaturation_countable_cover
end
end GinibrePoincare
