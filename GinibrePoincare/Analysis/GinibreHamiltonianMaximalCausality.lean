module

public import GinibrePoincare.Analysis.GinibreHamiltonianMaximalGlobal

@[expose] public section

/-! Causality of the actual uniquely glued maximal solution before either lifetime. -/
open Set MeasureTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem ginibreDrivenMaximalPath_noise_causal {n : ℕ} {α : ℝ}
    {N M : ℝ → Configuration n} {z : Configuration n} (T : ℝ≥0)
    (hN : (T : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N z)
    (hM : (T : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α M z)
    (hnoise : EqOn N M (Icc 0 (T : ℝ))) :
    EqOn (ginibreDrivenMaximalPath n α N z) (ginibreDrivenMaximalPath n α M z)
      (Icc 0 (T : ℝ)) := by
  have hX := ginibreDrivenMaximalPath_segment T hN
  have hY := ginibreDrivenMaximalPath_segment T hM
  apply ginibreDrivenPath_finite_interval_unique n α z N _ _ T T.property hX.1 hY.1
    (fun t ht => (hX.2.2 t ht).1) (fun t ht => (hY.2.2 t ht).1)
    (fun t ht => (hX.2.2 t ht).2.2)
  intro t ht
  rw [hnoise ht]
  exact (hY.2.2 t ht).2.2

 theorem GinibreDrivenSegment.horizon_lt_lifetime {n : ℕ} {α : ℝ}
    {N : ℝ → Configuration n} {z : Configuration n} {T : ℝ≥0} {X : ℝ → Configuration n}
    (hX : GinibreDrivenSegment n α N z T X) (hN : Continuous N) (hN0 : N 0 = 0) :
    (T : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N z := by
  by_cases hT : T = 0
  · subst T
    have hz : CollisionFree z := by rw [← hX.2.1]; exact (hX.2.2 0 (by simp)).1
    simpa using ginibreDrivenMaximalLifetime_pos n α N hN hN0 z hz
  · have ht : 0 < (T : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hT)
    let K := X '' Icc 0 (T : ℝ)
    have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hX.1
    have hcf : ∀ y ∈ K, CollisionFree y := by
      rintro y ⟨t, ht, rfl⟩
      exact (hX.2.2 t ht).1
    obtain ⟨δ, hδ, U, he, hc, hp⟩ := ginibreDrivenPath_compact_extend_beyond n α N X hN T ht
      (hX.1.mono Ico_subset_Icc_self) (fun t ht => (hX.2.2 t ⟨ht.1, ht.2.le⟩).2.1)
      (fun t ht => by rw [hX.2.1]; exact (hX.2.2 t ⟨ht.1, ht.2.le⟩).2.2)
      K hK hcf (fun t ht => ⟨t, ⟨ht.1, ht.2.le⟩, rfl⟩)
    let S : ℝ≥0 := ⟨(T : ℝ)+δ, by positivity⟩
    have hU0 : U 0 = z := (he ⟨le_rfl, ht⟩).trans hX.2.1
    have hS : S ∈ ginibreDrivenHorizons n α N z := by
      refine ⟨U, hc, hU0, ?_⟩
      intro t ht
      have hu := hp t ht
      exact ⟨hu.1, hu.2.1, by simpa only [hU0] using hu.2.2⟩
    apply lt_of_lt_of_le _ (ginibreDrivenHorizons_le_lifetime hS)
    apply ENNReal.coe_lt_coe.mpr
    change T < ⟨(T : ℝ)+δ, _⟩
    exact_mod_cast (lt_add_of_pos_right (T : ℝ) hδ)

end
end GinibrePoincare
