module

public import GinibrePoincare.Analysis.GinibreHamiltonianChapmanKolmogorov

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem ginibreDrivenHamiltonianBoundedStop_eventually_eq_cap {n : ℕ} (hn : 0 < n)
    (α : ℝ) (N : GinibreContinuousNoise n) (z : Configuration n) (hz : CollisionFree z)
    (hLife : ginibreDrivenMaximalLifetime n α N.val z=⊤) (T : ℝ≥0) :
    ∃ C : ℝ, ∀ R > C, ginibreHamiltonian n z ≤ R ∧
      ginibreDrivenHamiltonianBoundedStop n α N.val z R T=T := by
  have hT : (T : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N.val z := by simp [hLife]
  let H : ℝ≥0 → ℝ := fun t => ginibreHamiltonian n
    (ginibreDrivenMaximalValue n α N.val z (min t T))
  have hH : Continuous H := ginibreDrivenHamiltonianPrefix_continuous T hT
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hH.continuousOn
  refine ⟨|ginibreHamiltonian n z|+|C|+1,?_⟩
  intro R hR
  have hzR : ginibreHamiltonian n z ≤ R := by linarith [le_abs_self (ginibreHamiltonian n z), abs_nonneg C]
  refine ⟨hzR,?_⟩
  have hnot : ¬ginibreDrivenHamiltonianFirstLevel n α N.val z R ≤ (T : ℝ≥0∞) := by
    intro hh
    rcases (ginibreDrivenHamiltonianFirstLevel_le_iff_lifetime hn α N.val N.val.continuous N.property z hz R hzR T).mp hh with hbad | ⟨_, t, ht, hvalue⟩
    · simpa [hLife] using hbad
    · have hb := hC t ht
      change ‖H t‖ ≤ C at hb
      simp only [H, min_eq_left ht.2, Real.norm_eq_abs] at hb
      have hup := (le_abs_self _).trans hb
      linarith [le_abs_self C, abs_nonneg (ginibreHamiltonian n z)]
  unfold ginibreDrivenHamiltonianBoundedStop
  rw [min_eq_left (le_of_lt (lt_of_not_ge hnot)), ENNReal.toNNReal_coe]

end
end GinibrePoincare
