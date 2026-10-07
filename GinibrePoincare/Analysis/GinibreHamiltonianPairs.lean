module

public import GinibrePoincare.Analysis.GinibreHamiltonian

@[expose] public section

/-! Identification with the paper's unordered-pair logarithmic Hamiltonian. -/
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem ginibreHamiltonian_eq_pairwise_log {n : ℕ} (z : Configuration n)
    (hz : CollisionFree z) :
    ginibreHamiltonian n z = (n : ℝ)*configurationNormSq z -
      2*∑ i : Fin n, ∑ j ∈ Finset.Ioi i, Real.log ‖z j-z i‖ := by
  unfold ginibreHamiltonian vandermondeWeight
  rw [vandermonde_eq_product]
  simp_rw [map_prod Complex.normSq]
  rw [Real.log_prod]
  · congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.log_prod (fun j hj => fun h =>
      (ne_of_gt (Finset.mem_Ioi.mp hj))
        (hz (sub_eq_zero.mp (Complex.normSq_eq_zero.mp h))))]
    simp_rw [Complex.normSq_eq_norm_sq, Real.log_pow]
    simp only [Nat.cast_ofNat, Finset.mul_sum]
  · intro i hi
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact fun h => (ne_of_gt (Finset.mem_Ioi.mp hj))
      (hz (sub_eq_zero.mp (Complex.normSq_eq_zero.mp h)))

end
end GinibrePoincare
