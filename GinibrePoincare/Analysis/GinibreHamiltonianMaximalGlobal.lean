module

public import GinibrePoincare.Analysis.GinibreHamiltonianMaximalBlowup

@[expose] public section

/-! The constructed maximal path is an actual global solution when its lifespan is infinite. -/
open Set MeasureTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem ginibreDrivenMaximalPath_global_of_lifetime_top {n : ℕ} {α : ℝ}
    {N : ℝ → Configuration n} {z : Configuration n}
    (hglobal : ginibreDrivenMaximalLifetime n α N z = ⊤) :
    Continuous (ginibreDrivenMaximalPath n α N z) ∧
      ginibreDrivenMaximalPath n α N z 0 = z ∧
      (∀ t : ℝ, 0 ≤ t → CollisionFree (ginibreDrivenMaximalPath n α N z t)) ∧
      IsGinibreDrivenPath n α N (ginibreDrivenMaximalPath n α N z) := by
  have hdom : ginibreDrivenMaximalDomain n α N z = Ici 0 := by
    ext t
    simp only [ginibreDrivenMaximalDomain, Set.mem_setOf_eq, Set.mem_Ici, hglobal,
      ENNReal.ofReal_lt_top, and_true]
  have hcont : ContinuousOn (ginibreDrivenMaximalPath n α N z) (Ici 0) := by
    rw [← hdom]
    exact ginibreDrivenMaximalPath_continuousOn n α N z
  have hc := hcont.comp_continuous (continuous_id.max continuous_const)
    (fun t => le_max_right t (0 : ℝ))
  have hclip : (fun t => ginibreDrivenMaximalPath n α N z (max t 0)) =
      ginibreDrivenMaximalPath n α N z := by
    funext t
    simp only [ginibreDrivenMaximalPath]
    congr 1
    apply Subtype.ext
    simp [Real.coe_toNNReal', max_eq_left (le_max_right t 0)]
  change Continuous (fun t => ginibreDrivenMaximalPath n α N z (max t 0)) at hc
  rw [hclip] at hc
  have h0 : ginibreDrivenMaximalPath n α N z 0 = z :=
    (ginibreDrivenMaximalPath_segment 0 (by simp [hglobal])).2.1
  have hp (t : ℝ) (ht : 0 ≤ t) :=
    ginibreDrivenMaximalPath_equation (n := n) (α := α) (N := N) (z := z)
      (by rw [hdom]; exact ht)
  refine ⟨hc, h0, fun t ht => (hp t ht).1, ?_⟩
  exact ⟨fun t ht => (hp t ht).2.1, fun t ht => by rw [h0]; exact (hp t ht).2.2⟩

end
end GinibrePoincare
