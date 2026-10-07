module

public import GinibrePoincare.Analysis.GinibreHamiltonianInteractionPotential

@[expose] public section

namespace GinibrePoincare
noncomputable section

/-- The genuine interaction likelihood initial factor cancels the
Vandermonde density of Ginibre relative to its Gaussian reference. -/
theorem ginibreInteraction_initial_density_cancellation {n : ℕ}
    (z : Configuration n) (hz : CollisionFree z) :
    vandermondeWeight z * Real.exp (ginibreInteractionPotential n z) = 1 := by
  rw [ginibreInteractionPotential, Real.exp_neg,
    Real.exp_log (vandermondeWeight_pos_of_collisionFree z hz)]
  exact mul_inv_cancel₀ (ne_of_gt (vandermondeWeight_pos_of_collisionFree z hz))

theorem ginibreInteraction_initial_action_cancellation {n : ℕ}
    (z : Configuration n) (hz : CollisionFree z) (action : ℝ) :
    vandermondeWeight z * (Real.exp (ginibreInteractionPotential n z) * action) = action := by
  rw [← mul_assoc, ginibreInteraction_initial_density_cancellation z hz, one_mul]

#print axioms ginibreInteraction_initial_action_cancellation
end
end GinibrePoincare
