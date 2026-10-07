module

public import GinibrePoincare.Analysis.MatrixUnitaryCenteredPhaseFactorization
public import GinibrePoincare.Analysis.MatrixSchurProductIntegration

@[expose] public section

open Matrix NormedSpace Filter Set
open scoped Matrix Matrix.Norms.Operator Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 10000

def matrixUnitaryFlagSaturation (n : ℕ) (V : Set (SchurLowerIndex n → ℂ)) :
    Set (Matrix (Fin n) (Fin n) ℂ) :=
  {U | ∃ x ∈ V, ∃ D : Matrix (Fin n) (Fin n) ℂ,
    D ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ (∀ i j, i ≠ j → D i j = 0) ∧
      U = matrixSchurExponentialFrame n x * D}

theorem matrixDiagonalPhase_unitary (n : ℕ) (d : Fin n → ℝ) :
    exp (matrixSkewDiagonalCLM n d) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hh := matrixUnitaryPhaseParameter_unitary n ((0 : SchurLowerIndex n → ℂ), d)
  simpa [matrixUnitaryPhaseParameter, ← schurSkewCLM_apply, exp_zero] using hh

theorem matrixDiagonalPhase_diagonal (n : ℕ) (d : Fin n → ℝ) (i j : Fin n) (hij : i ≠ j) :
    exp (matrixSkewDiagonalCLM n d) i j = 0 := by
  rw [matrixSkewDiagonalCLM_apply, Matrix.exp_diagonal]
  simp [hij]

/-- The phase-saturated angular section is open within the actual unitary group. -/
theorem matrixUnitaryFlagSaturation_isOpen (n : ℕ) (V : Set (SchurLowerIndex n → ℂ))
    (hV : IsOpen V)
    (hsource : ∀ x ∈ V, (x, (0 : Fin n → ℝ)) ∈ (matrixUnitaryPhaseLocalChart n).source)
    (hden : ∀ x ∈ V, IsUnit (matrixSchurExponentialFrame n x + 1)) :
    IsOpen {U : Matrix.unitaryGroup (Fin n) ℂ | (U : Matrix (Fin n) (Fin n) ℂ) ∈ matrixUnitaryFlagSaturation n V} := by
  apply isOpen_iff_mem_nhds.mpr
  intro U hU
  obtain ⟨x, hx, D, hDunit, hDdiag, hrep⟩ := hU
  let M := Matrix (Fin n) (Fin n) ℂ
  have hDD : D * Dᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hDunit
  have hDD' : Dᴴ * D = 1 := Matrix.mem_unitaryGroup_iff'.mp hDunit
  have hDstar : Dᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    apply Matrix.mem_unitaryGroup_iff'.mpr
    change (Dᴴ)ᴴ * Dᴴ = 1
    rw [Matrix.conjTranspose_conjTranspose]
    exact hDD
  have hpbase : matrixUnitaryPhaseParameter n (x, (0 : Fin n → ℝ)) =
      matrixSchurExponentialFrame n x := by
    simp [matrixUnitaryPhaseParameter, matrixSchurExponentialFrame, exp_zero]
  have hN : V ×ˢ (Set.univ : Set (Fin n → ℝ)) ∈ 𝓝 (x, (0 : Fin n → ℝ)) :=
    prod_mem_nhds (hV.mem_nhds hx) (Filter.univ_mem)
  have hcent := matrixUnitary_centered_phase_factorization n (x, 0)
    (hsource x hx) (hpbase.symm ▸ hden x hx) (V ×ˢ Set.univ) hN
  rw [hpbase] at hcent
  have hmul : ContinuousAt (fun Z : M => Z * Dᴴ) (U : M) := by fun_prop
  have hbase : (U : M) * Dᴴ = matrixSchurExponentialFrame n x := by
    rw [hrep, Matrix.mul_assoc, hDD, Matrix.mul_one]
  change Tendsto (fun Z : M => Z * Dᴴ) (𝓝 (U : M)) (𝓝 ((U : M) * Dᴴ)) at hmul
  rw [hbase] at hmul
  have hpre := hmul hcent
  have hevent : ∀ᶠ Z : M in 𝓝 (U : M),
      Z ∈ Matrix.unitaryGroup (Fin n) ℂ → Z ∈ matrixUnitaryFlagSaturation n V := by
    filter_upwards [hpre] with Z hZ
    intro hZunit
    obtain ⟨p, hp, he⟩ := hZ ((Matrix.unitaryGroup (Fin n) ℂ).mul_mem hZunit hDstar)
    refine ⟨p.1, hp.1, exp (matrixSkewDiagonalCLM n p.2) * D,
      (Matrix.unitaryGroup (Fin n) ℂ).mul_mem (matrixDiagonalPhase_unitary n p.2) hDunit, ?_, ?_⟩
    · intro i j hij
      rw [matrixSkewDiagonalCLM_apply, Matrix.exp_diagonal, Matrix.diagonal_mul, hDdiag i j hij, mul_zero]
    · calc
        Z = (Z * Dᴴ) * D := by rw [Matrix.mul_assoc, hDD', Matrix.mul_one]
        _ = matrixUnitaryPhaseParameter n p * D := by rw [he]
        _ = _ := by rw [matrixUnitaryPhaseParameter, Matrix.mul_assoc]; rfl
  have hcoe : ContinuousAt (fun Z : Matrix.unitaryGroup (Fin n) ℂ => (Z : M)) U :=
    continuous_subtype_val.continuousAt
  filter_upwards [hcoe hevent] with Z hZ
  exact hZ Z.property

#print axioms matrixUnitaryFlagSaturation_isOpen
end
end GinibrePoincare
