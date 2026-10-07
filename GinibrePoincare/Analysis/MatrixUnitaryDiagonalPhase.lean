module

public import GinibrePoincare.Analysis.MatrixUnitarySmallPhaseFactorization

@[expose] public section

open Matrix NormedSpace Filter Set
open scoped Matrix Matrix.Norms.Operator Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem matrixUnitaryPhaseParameter_diagonal_lower_zero (n : ℕ)
    (p : MatrixSkewCoordinates n)
    (hp : p.1 ∈ (matrixUnitaryLowerLocalChart n).source)
    (hd : ∀ i j, i ≠ j → matrixUnitaryPhaseParameter n p i j = 0) : p.1 = 0 := by
  let R := exp (matrixSkewDiagonalCLM n p.2)
  have hR : R = Matrix.diagonal (exp (fun i => (p.2 i : ℂ) * Complex.I)) := by
    dsimp only [R]
    rw [matrixSkewDiagonalCLM_apply, Matrix.exp_diagonal]
  have hunit : R ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    have hh := matrixUnitaryPhaseParameter_unitary n ((0 : SchurLowerIndex n → ℂ), p.2)
    simpa [matrixUnitaryPhaseParameter, ← schurSkewCLM_apply, map_zero, exp_zero] using hh
  have hRR : R * Rᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hunit
  have he : exp (schurSkewCombination p.1) = matrixUnitaryPhaseParameter n p * Rᴴ := by
    change _ = (exp (schurSkewCombination p.1) * R) * Rᴴ
    rw [Matrix.mul_assoc, hRR, Matrix.mul_one]
  apply matrixUnitaryLowerLocalChart_diagonal_iff_zero n p.1 hp
  intro i j hij
  rw [he, hR, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, hd i j hij, zero_mul]

/-- Diagonal unitary matrices near the identity have arbitrarily small diagonal phase
coordinates, with no residual lower skew coordinates. -/
theorem matrixUnitary_diagonal_phase_small (n : ℕ)
    (W : Set (Fin n → ℝ)) (hW : W ∈ 𝓝 0) :
    ∀ᶠ U : Matrix (Fin n) (Fin n) ℂ in 𝓝 1,
      U ∈ Matrix.unitaryGroup (Fin n) ℂ →
      (∀ i j, i ≠ j → U i j = 0) →
      ∃ d ∈ W, U = exp (matrixSkewDiagonalCLM n d) := by
  let N := (matrixUnitaryLowerLocalChart n).source ×ˢ W
  have hN : N ∈ 𝓝 (0 : MatrixSkewCoordinates n) :=
    prod_mem_nhds
      ((matrixUnitaryLowerLocalChart n).open_source.mem_nhds
        (matrixUnitaryLowerLocalChart_zero_mem_source n)) hW
  filter_upwards [matrixUnitary_local_phase_factorization_small n N hN] with U hU
  intro hunit hdiag
  obtain ⟨p, hp, he⟩ := hU hunit
  have hzero : p.1 = 0 := matrixUnitaryPhaseParameter_diagonal_lower_zero n p hp.1
    (by simpa only [he] using hdiag)
  refine ⟨p.2, hp.2, ?_⟩
  rw [← he, matrixUnitaryPhaseParameter, hzero]
  simp [← schurSkewCLM_apply, map_zero, exp_zero]

#print axioms matrixUnitary_diagonal_phase_small
end
end GinibrePoincare
