module

public import GinibrePoincare.Analysis.GinibreHamiltonianJointEvaluation
public import GinibrePoincare.Analysis.GinibreDrivenPathRestart

@[expose] public section

/-! Genuine canonical restart of global original additive-noise solutions. -/
open Set MeasureTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem ginibreDrivenPath_canonical_global {n : ℕ} {α : ℝ}
    {N X : ℝ → Configuration n} (hX : Continuous X)
    (hFree : ∀ t : ℝ, 0 ≤ t → CollisionFree (X t))
    (hEq : IsGinibreDrivenPath n α N X) :
    ginibreDrivenMaximalLifetime n α N (X 0) = ⊤ ∧
    ∀ t : ℝ≥0, ginibreDrivenMaximalValue n α N (X 0) t = X t := by
  have hSeg (T : ℝ≥0) : GinibreDrivenSegment n α N (X 0) T X :=
    ⟨hX.continuousOn, rfl, fun t ht => ⟨hFree t ht.1, hEq.1 t ht.1, hEq.2 t ht.1⟩⟩
  have hLife : ginibreDrivenMaximalLifetime n α N (X 0) = ⊤ := by
    by_contra hfin
    let L := ginibreDrivenMaximalLifetime n α N (X 0)
    let T := L.toNNReal+1
    have hb := ginibreDrivenHorizons_le_lifetime
      (show T ∈ ginibreDrivenHorizons n α N (X 0) from ⟨_, hSeg T⟩)
    change (T : ℝ≥0∞) ≤ L at hb
    have hfinL : L ≠ ⊤ := hfin
    rw [← ENNReal.coe_toNNReal hfinL] at hb
    have hbad := ENNReal.coe_le_coe.mp hb
    change L.toNNReal+1 ≤ L.toNNReal at hbad
    exact (not_le_of_gt (lt_add_of_pos_right L.toNNReal zero_lt_one)) hbad
  exact ⟨hLife, fun t => ginibreDrivenMaximalValue_eq_segment (hSeg t) t le_rfl (by simp [hLife])⟩

theorem ginibreDrivenPath_canonical_restart {n : ℕ} {α : ℝ}
    {N X : ℝ → Configuration n} (hX : Continuous X)
    (hFree : ∀ t : ℝ, 0 ≤ t → CollisionFree (X t))
    (hEq : IsGinibreDrivenPath n α N X) (s : ℝ≥0) :
    ginibreDrivenMaximalLifetime n α (fun t => N (s+t)-N s) (X s) = ⊤ ∧
    ∀ t : ℝ≥0, ginibreDrivenMaximalValue n α (fun u => N (s+u)-N s) (X s) t = X (s+t) := by
  have h := ginibreDrivenPath_canonical_global
    (hX.comp (continuous_const.add continuous_id))
    (fun t ht => hFree (s+t) (add_nonneg s.property ht))
    (ginibreDrivenPath_shift n α N X hEq s s.property)
  simpa only [Function.comp_def, Pi.add_apply, id_eq, add_zero] using h

end
end GinibrePoincare
