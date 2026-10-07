module

public import GinibrePoincare.Analysis.GinibreStochasticCompactTaylorMeasurability
public import GinibrePoincare.Analysis.GinibreHamiltonianGenerator
public import GinibrePoincare.Analysis.GinibreHamiltonianDrift

@[expose] public section

/-! The genuine Itô correction has exactly the paper's implemented generator. -/
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000

theorem ginibreLangevin_fderiv_generator {n : ℕ} (hn : 0 < n) (α : ℝ)
    (f : Configuration n → ℝ) (z : Configuration n) (hz : CollisionFree z) :
    fderiv ℝ f z (ginibreLangevinDrift n α z)+
      (α/(n : ℝ)^2)*configurationLaplacian f z =
      ginibreRealPaperSpeedGenerator n α f z := by
  rw [ginibreConfiguration_fderiv_coordinate_sum]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  change (∑ j : Fin n, ((ginibreLangevinDrift n α z j).re*fderiv ℝ f z (realCoordinateDirection j)+
    (ginibreLangevinDrift n α z j).im*fderiv ℝ f z (imaginaryCoordinateDirection j)))+
      (α/(n : ℝ)^2)*configurationLaplacian f z = ginibreRealPaperSpeedGenerator n α f z
  simp_rw [ginibreLangevinDrift_re_hamiltonian hn α z hz,
    ginibreLangevinDrift_im_hamiltonian hn α z hz,
    fderiv_ginibreHamiltonian_realCoordinate hn z hz,
    fderiv_ginibreHamiltonian_imaginaryCoordinate hn z hz]
  unfold ginibreRealPaperSpeedGenerator
  rw [ginibrePregenerator_eq_laplacian_sub_drift]
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  simp only [mul_sub]
  have he : ∑ j : Fin n,
      (-(α/(n : ℝ)^2)*((n : ℝ)*ginibreRealDriftCoordinate n j z)*
          fderiv ℝ f z (realCoordinateDirection j)+
        -(α/(n : ℝ)^2)*((n : ℝ)*ginibreImagDriftCoordinate n j z)*
          fderiv ℝ f z (imaginaryCoordinateDirection j)) =
      -(α/(n : ℝ))*∑ j : Fin n,
        (ginibreRealDriftCoordinate n j z*fderiv ℝ f z (realCoordinateDirection j)+
          ginibreImagDriftCoordinate n j z*fderiv ℝ f z (imaginaryCoordinateDirection j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    field_simp [hne]
    ring
  rw [he]
  field_simp [hne]
  ring
end
end GinibrePoincare
