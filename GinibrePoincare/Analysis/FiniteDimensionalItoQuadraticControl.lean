module

public import GinibrePoincare.Analysis.FiniteDimensionalItoConfiguration
public import GinibrePoincare.Analysis.FiniteDimensionalItoDriftVariation

@[expose] public section

namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E]

theorem itoNorm_add_sq_le (a b : E) : ‖a+b‖^2 ≤ 2*‖a‖^2+2*‖b‖^2 := by
  have h := norm_add_le a b
  have ha := norm_nonneg a
  have hb := norm_nonneg b
  have hab := norm_nonneg (a+b)
  have hsq := sq_nonneg (‖a‖-‖b‖)
  nlinarith

/-- Actual configuration quadratic sums are controlled by actual scalar noise
quadratic sums and actual drift variation. -/
theorem itoConfigurationQuadraticSum_le {n : ℕ} {ι : Type*}
    (s : Finset ι) (a b : ι → Configuration n) (m : ℝ)
    (hb : ∀ i ∈ s, ‖b i‖ ≤ m) :
    ∑ i ∈ s, ‖a i+b i‖^2 ≤
      2*(∑ j : Fin n × Fin 2, ∑ i ∈ s, (configurationEuclideanLinearEquiv n (a i) j)^2) +
        2*m*(∑ i ∈ s, ‖b i‖) := by
  calc
    _ ≤ ∑ i ∈ s, (2*‖a i‖^2+2*‖b i‖^2) :=
      Finset.sum_le_sum (fun i hi => itoNorm_add_sq_le _ _)
    _ ≤ ∑ i ∈ s, (2*(∑ j : Fin n × Fin 2,
        (configurationEuclideanLinearEquiv n (a i) j)^2)+2*m*‖b i‖) := by
      apply Finset.sum_le_sum
      intro i hi
      have ha := itoConfiguration_norm_sq_le_coordinate_sum (a i)
      have hd := mul_le_mul_of_nonneg_right (hb i hi) (norm_nonneg (b i))
      nlinarith
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [Finset.sum_comm]

end
end GinibrePoincare
