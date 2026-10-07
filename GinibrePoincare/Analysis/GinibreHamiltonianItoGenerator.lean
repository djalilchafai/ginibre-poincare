module

public import GinibrePoincare.Analysis.GinibreHamiltonianGenerator
public import GinibrePoincare.Analysis.GinibreHamiltonianDrift
public import GinibrePoincare.Analysis.GinibreDirectionalCoordinates

@[expose] public section

/-! The actual Itô drift and Hessian trace equal the proved Hamiltonian generator. -/
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem fderiv_ginibreHamiltonian_langevinDrift {n : ℕ} (hn : 0 < n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z) :
    fderiv ℝ (ginibreHamiltonian n) z (ginibreLangevinDrift n α z) =
      -(α/(n : ℝ)^2)*ginibreHamiltonianGradientNormSq n z := by
  rw [fderiv_ginibreDirection_decomposition]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, ginibreDirectionCoefficient,
    ginibreCoordinateDirection, if_pos rfl, if_neg (by decide : (1 : Fin 2) ≠ 0)]
  unfold ginibreHamiltonianGradientNormSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [ginibreLangevinDrift_re_hamiltonian hn α z hz j,
    ginibreLangevinDrift_im_hamiltonian hn α z hz j]
  simp only [if_true]
  ring

 theorem ginibreHamiltonian_ito_generator {n : ℕ} (hn : 0 < n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z) :
    fderiv ℝ (ginibreHamiltonian n) z (ginibreLangevinDrift n α z) +
      (α/(n : ℝ)^2)*configurationLaplacian (ginibreHamiltonian n) z =
      ginibreRealPaperSpeedGenerator n α (ginibreHamiltonian n) z := by
  rw [fderiv_ginibreHamiltonian_langevinDrift hn α z hz,
    ginibreHamiltonian_laplacian z hz, ginibreRealPaperSpeedGenerator_hamiltonian hn α z hz]
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hne]
  ring

end
end GinibrePoincare
