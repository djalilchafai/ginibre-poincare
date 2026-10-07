module

public import GinibrePoincare.Analysis.GinibreHamiltonianLaplacian

@[expose] public section

/-! Exact Hamiltonian generator and the uniform Lyapunov generator bound. -/
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Squared Euclidean gradient, in the actual real coordinate directions. -/
def ginibreHamiltonianGradientNormSq (n : ℕ) (z : Configuration n) : ℝ :=
  ∑ j : Fin n,
    ((fderiv ℝ (ginibreHamiltonian n) z (realCoordinateDirection j))^2 +
    (fderiv ℝ (ginibreHamiltonian n) z (imaginaryCoordinateDirection j))^2)

theorem ginibreHamiltonianGradientNormSq_nonneg (n : ℕ) (z : Configuration n) :
    0 ≤ ginibreHamiltonianGradientNormSq n z := by
  exact Finset.sum_nonneg (fun j _ => add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem ginibrePregenerator_hamiltonian {n : ℕ} (hn : 0 < n)
    (z : Configuration n) (hz : CollisionFree z) :
    ginibrePregenerator n (ginibreHamiltonian n) z =
      4*(n : ℝ) - ginibreHamiltonianGradientNormSq n z/(n : ℝ) := by
  rw [ginibrePregenerator_eq_laplacian_sub_drift,
    ginibreHamiltonian_laplacian z hz]
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hs : (∑ j : Fin n,
      (ginibreRealDriftCoordinate n j z *
        fderiv ℝ (ginibreHamiltonian n) z (realCoordinateDirection j) +
      ginibreImagDriftCoordinate n j z *
        fderiv ℝ (ginibreHamiltonian n) z (imaginaryCoordinateDirection j))) =
      ginibreHamiltonianGradientNormSq n z/(n : ℝ) := by
    unfold ginibreHamiltonianGradientNormSq
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    rw [fderiv_ginibreHamiltonian_realCoordinate hn z hz,
      fderiv_ginibreHamiltonian_imaginaryCoordinate hn z hz]
    field_simp [hne]
    <;> ring
  rw [hs]
  congr 1
  field_simp [hne]
  <;> ring

/-- The real generator at the paper's speed parameter. -/
def ginibreRealPaperSpeedGenerator (n : ℕ) (α : ℝ)
    (f : Configuration n → ℝ) (z : Configuration n) : ℝ :=
  (α/(n : ℝ))*ginibrePregenerator n f z

theorem ginibreRealPaperSpeedGenerator_hamiltonian {n : ℕ} (hn : 0 < n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z) :
    ginibreRealPaperSpeedGenerator n α (ginibreHamiltonian n) z =
      4*α - (α/(n : ℝ)^2)*ginibreHamiltonianGradientNormSq n z := by
  unfold ginibreRealPaperSpeedGenerator
  rw [ginibrePregenerator_hamiltonian hn z hz]
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hne]
  <;> ring

theorem ginibreRealPaperSpeedGenerator_hamiltonian_le {n : ℕ} (hn : 0 < n)
    (α : ℝ) (hα : 0 ≤ α) (z : Configuration n) (hz : CollisionFree z) :
    ginibreRealPaperSpeedGenerator n α (ginibreHamiltonian n) z ≤ 4*α := by
  rw [ginibreRealPaperSpeedGenerator_hamiltonian hn α z hz]
  exact sub_le_self _ (mul_nonneg (div_nonneg hα (sq_nonneg _))
    (ginibreHamiltonianGradientNormSq_nonneg n z))

end
end GinibrePoincare
