module

public import GinibrePoincare.Analysis.GinibreStochasticCenterDirection

@[expose] public section

/-! Actual normalization of the repeated center in original coordinate noise. -/
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000

theorem ginibreRepeatedCenterEuclidean_norm_sq (n : ℕ) (z : Configuration n) :
    ‖configurationEuclideanEquiv n (ginibreRepeatedCenterCLM n z)‖^2 =
      (n : ℝ)*ginibreCenterSquared n z := by
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, configurationEuclideanEquiv_apply_zero,
    configurationEuclideanEquiv_apply_one, ginibreRepeatedCenterCLM,
    ContinuousLinearMap.pi_apply, coordinateSumCLM_apply]
  simp [ginibreCenterSquared, Complex.normSq_apply]
  ring

theorem ginibreRepeatedCenterEuclidean_norm (n : ℕ) (z : Configuration n) :
    ‖configurationEuclideanEquiv n (ginibreRepeatedCenterCLM n z)‖ =
      Real.sqrt ((n : ℝ)*ginibreCenterSquared n z) := by
  rw [← ginibreRepeatedCenterEuclidean_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem ginibreCenterRadialDirection_apply {n : ℕ} (hn : 0 < n)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (z : Configuration n)
    (hz : ginibreCenterSquared n z ≠ 0) (i : Fin n) :
    ginibreCenterRadialDirection n e z (i, 0) =
      (Real.sqrt ((n : ℝ)*ginibreCenterSquared n z))⁻¹*(coordinateSum z).re ∧
    ginibreCenterRadialDirection n e z (i, 1) =
      (Real.sqrt ((n : ℝ)*ginibreCenterSquared n z))⁻¹*(coordinateSum z).im := by
  have hne : configurationEuclideanEquiv n (ginibreRepeatedCenterCLM n z) ≠ 0 := by
    intro h
    have hh := ginibreRepeatedCenterEuclidean_norm_sq n z
    rw [h, norm_zero, zero_pow (by norm_num)] at hh
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    exact hz ((mul_eq_zero.mp hh.symm).resolve_left hnR)
  unfold ginibreCenterRadialDirection brownianRadialUnitVector
  rw [if_neg hne, ginibreRepeatedCenterEuclidean_norm]
  simp only [PiLp.smul_apply, smul_eq_mul, configurationEuclideanEquiv_apply_zero,
    configurationEuclideanEquiv_apply_one, ginibreRepeatedCenterCLM,
    ContinuousLinearMap.pi_apply, coordinateSumCLM_apply]
  exact ⟨trivial, trivial⟩

#print axioms ginibreCenterRadialDirection_apply
#print axioms ginibreRepeatedCenterEuclidean_norm_sq
#print axioms ginibreRepeatedCenterEuclidean_norm
end
end GinibrePoincare
