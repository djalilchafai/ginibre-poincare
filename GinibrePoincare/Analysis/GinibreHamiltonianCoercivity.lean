module

public import GinibrePoincare.Analysis.GinibreHamiltonianCollision
public import GinibrePoincare.Analysis.GinibreDensityBound

@[expose] public section

/-! A genuine quadratic lower bound for the Hamiltonian, including repulsion. -/
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def ginibreHamiltonianLowerBoundConstant (n : ℕ) : ℝ :=
  (n : ℝ)^2 * (Real.log (8*(n : ℝ))-1) + (n : ℝ)/2

theorem ginibreHamiltonian_quadratic_lower_bound {n : ℕ} (hn : 0 < n)
    (z : Configuration n) (hz : CollisionFree z) :
    (n : ℝ)/2*configurationNormSq z - ginibreHamiltonianLowerBoundConstant n ≤
      ginibreHamiltonian n z := by
  have hN : 0 < (n : ℝ) := by exact_mod_cast hn
  have hS := configurationNormSq_nonneg z
  have hp : 0 < (configurationNormSq z+1)/(2*(n : ℝ)) :=
    div_pos (by linarith) (by positivity)
  have hlog := Real.log_le_sub_one_of_pos hp
  have hprod : 4*(configurationNormSq z+1) =
      (8*(n : ℝ))*((configurationNormSq z+1)/(2*(n : ℝ))) := by
    field_simp
    <;> ring
  have hL : Real.log (4*(configurationNormSq z+1)) ≤
      Real.log (8*(n : ℝ)) + (configurationNormSq z+1)/(2*(n : ℝ))-1 := by
    rw [hprod, Real.log_mul (by positivity) (ne_of_gt hp)]
    linarith
  have hW := Real.log_le_log (vandermondeWeight_pos_of_collisionFree z hz)
    (vandermondeWeight_le_radius_bound n z)
  rw [Real.log_pow] at hW
  have hD : ((n*n : ℕ) : ℝ) = (n : ℝ)^2 := by push_cast; ring
  rw [hD] at hW
  have hB := mul_le_mul_of_nonneg_left hL (sq_nonneg (n : ℝ))
  have hcalc : (n : ℝ)^2 *
      (Real.log (8*(n : ℝ))+(configurationNormSq z+1)/(2*(n : ℝ))-1) =
      (n : ℝ)/2*configurationNormSq z + ginibreHamiltonianLowerBoundConstant n := by
    unfold ginibreHamiltonianLowerBoundConstant
    field_simp
    <;> ring
  rw [hcalc] at hB
  unfold ginibreHamiltonian
  linarith

theorem ginibreHamiltonian_bounded_below {n : ℕ} (hn : 0 < n)
    (z : Configuration n) (hz : CollisionFree z) :
    -ginibreHamiltonianLowerBoundConstant n ≤ ginibreHamiltonian n z := by
  have h := ginibreHamiltonian_quadratic_lower_bound hn z hz
  have hN : 0 ≤ (n : ℝ)/2 := by positivity
  have hs := mul_nonneg hN (configurationNormSq_nonneg z)
  linarith

end
end GinibrePoincare
