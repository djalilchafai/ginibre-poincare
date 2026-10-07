module

public import GinibrePoincare.Analysis.MatrixGaussianLSI
public import GinibrePoincare.Analysis.MatrixRealDifferential

@[expose] public section

open Matrix
open scoped BigOperators Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem matrixTrace_entry_direction {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) (z : ℂ) :
    trace (C * Matrix.of (Pi.single i (Pi.single j z))) = C j i * z := by
  classical
  simp [Matrix.trace, Matrix.mul_apply, Pi.single_apply, ite_apply, Pi.zero_apply, eq_comm]

theorem matrixTrace_real_coordinate_energy (n : ℕ) (C : Matrix (Fin n) (Fin n) ℂ) :
    (∑ p : MatrixRealIndex n,
      (2 * (trace (C * Matrix.of (matrixRealCoordinates n (Pi.single p 1)))).re) ^ 2) =
      4 * matrixHSNormSq C := by
  classical
  rw [Fintype.sum_sigma]
  simp_rw [Fintype.sum_sigma, Fin.sum_univ_two, matrixRealCoordinates_direction,
    matrixTrace_entry_direction]
  rw [matrixHSNormSq_eq_sum]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp [Complex.normSq_apply, Complex.mul_I_re]
  ring

/-- The exact overlap energy of an actual differentiable spectral lift. -/
theorem matrixLocalSpectralLift_energy (n : ℕ) (A : GinibreMatrixCoordinates n)
    (labels : GinibreMatrixCoordinates n → Fin n → ℂ) (F : (Fin n → ℂ) → ℝ)
    (hs : (Matrix.of A).charpoly.Separable) (hd : DifferentiableAt ℂ labels A)
    (hF : DifferentiableAt ℝ F (labels A))
    (hr : ∀ᶠ B in nhds A, ∀ i, (Matrix.of B).charpoly.eval (labels B i) = 0) :
    matrixRealGradientEnergy n (F ∘ labels) A =
      4 * matrixOverlapEnergy (fun i => matrixEigenvalueProjector n A (labels A i))
        (realDifferentialWirtinger (fderiv ℝ F (labels A))) := by
  classical
  let P := fun i => matrixEigenvalueProjector n A (labels A i)
  let a := realDifferentialWirtinger (fderiv ℝ F (labels A))
  rw [matrixOverlapEnergy_eq_HS]
  unfold matrixRealGradientEnergy directionalEnergy
  have he (p : MatrixRealIndex n) :
      fderiv ℝ (F ∘ labels) A (matrixRealCoordinates n (Pi.single p 1)) =
        2 * (trace (matrixProjectorCombination P a *
          Matrix.of (matrixRealCoordinates n (Pi.single p 1)))).re := by
    rw [matrixLocalSpectralLift_wirtinger n A _ labels F hs hd hF hr]
    simp [P, a, matrixProjectorCombination, Matrix.sum_mul, Matrix.smul_mul,
      Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  simp_rw [he]
  exact matrixTrace_real_coordinate_energy n (matrixProjectorCombination P a)

#print axioms matrixLocalSpectralLift_energy
end
end GinibrePoincare
