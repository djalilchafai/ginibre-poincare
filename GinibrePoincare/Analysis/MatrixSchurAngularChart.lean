module

public import GinibrePoincare.Analysis.MatrixUnitaryFlagSaturation

@[expose] public section

open Matrix NormedSpace Filter Set
open scoped Matrix Matrix.Norms.Operator Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

/-- An angular Schur chart is simultaneously injective, phase-saturated open, and
contained in the genuine phase-coordinate source and Cayley domain. -/
theorem matrixSchurAngularChart_exists (n : ℕ) :
    ∃ V : Set (SchurLowerIndex n → ℂ), IsOpen V ∧ 0 ∈ V ∧
      InjOn (matrixSchurFrameChart (matrixSchurExponentialFrame n) (0 : Matrix (Fin n) (Fin n) ℂ))
        (V ×ˢ matrixSchurSortedUpperDomain n) ∧
      (∀ x ∈ V, (x, (0 : Fin n → ℝ)) ∈ (matrixUnitaryPhaseLocalChart n).source) ∧
      (∀ x ∈ V, IsUnit (matrixSchurExponentialFrame n x + 1)) ∧
      IsOpen {U : Matrix.unitaryGroup (Fin n) ℂ |
        (U : Matrix (Fin n) (Fin n) ℂ) ∈ matrixUnitaryFlagSaturation n V} := by
  let X := SchurLowerIndex n → ℂ
  let M := Matrix (Fin n) (Fin n) ℂ
  obtain ⟨V0, hV0, hzero, hinj⟩ := matrixSchurSortedDomain_exists_injective n
  let S : Set X := {x | (x, (0 : Fin n → ℝ)) ∈ (matrixUnitaryPhaseLocalChart n).source}
  have hS : IsOpen S := (matrixUnitaryPhaseLocalChart n).open_source.preimage
    (continuous_id.prodMk continuous_const)
  have hS0 : (0 : X) ∈ S := matrixUnitaryPhaseLocalChart_zero_mem_source n
  let D : Set X := {x | (matrixSchurExponentialFrame n x + 1).det ≠ 0}
  have hcont : Continuous (fun x : X => (matrixSchurExponentialFrame n x + 1).det) := by
    have hQ := (matrixSchurExponentialFrame_differentiable n).continuous
    fun_prop
  have hD : IsOpen D := isOpen_ne_fun hcont continuous_const
  have hD0 : (0 : X) ∈ D := by
    change (matrixSchurExponentialFrame n 0 + 1).det ≠ 0
    have hQ0 : matrixSchurExponentialFrame n 0 = (1 : M) := by
      simp [matrixSchurExponentialFrame, ← schurSkewCLM_apply, exp_zero]
    rw [hQ0, ← two_smul ℂ (1 : M), Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ (by norm_num)
  let V := V0 ∩ S ∩ D
  have hV : IsOpen V := (hV0.inter hS).inter hD
  have hsource : ∀ x ∈ V, (x, (0 : Fin n → ℝ)) ∈ (matrixUnitaryPhaseLocalChart n).source :=
    fun x hx => hx.1.2
  have hden : ∀ x ∈ V, IsUnit (matrixSchurExponentialFrame n x + 1) := fun x hx =>
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hx.2)
  refine ⟨V, hV, ⟨⟨hzero, hS0⟩, hD0⟩, hinj.mono ?_, hsource, hden,
    matrixUnitaryFlagSaturation_isOpen n V hV hsource hden⟩
  intro p hp
  exact ⟨hp.1.1.1, hp.2⟩

theorem matrixUnitaryFlagSaturation_one {n : ℕ} (V : Set (SchurLowerIndex n → ℂ))
    (h0 : 0 ∈ V) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ matrixUnitaryFlagSaturation n V := by
  refine ⟨0, h0, 1, (Matrix.unitaryGroup (Fin n) ℂ).one_mem, ?_, ?_⟩
  · intro i j hij
    simp [hij]
  · simp [matrixSchurExponentialFrame, ← schurSkewCLM_apply, exp_zero]

#print axioms matrixSchurAngularChart_exists
end
end GinibrePoincare
