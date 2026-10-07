module

public import GinibrePoincare.Analysis.GinibreHamiltonianMaximalNoiseTopology

@[expose] public section

/-! Quantitative continuity of actual maximal solution values before death. -/
open Set Metric MeasureTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

 theorem ginibreDrivenMaximalValue_uniform_noise_continuity {n : ℕ} (hn : 0 < n)
    (α : ℝ) (N : ℝ → Configuration n) (z : Configuration n) (T : ℝ≥0)
    (hT : (T : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N z) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ M : ℝ → Configuration n, Continuous M → M 0 = 0 →
      (∀ t ∈ Icc 0 (T : ℝ), ‖N t-M t‖ ≤ δ) →
      (T : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α M z ∧
        ‖ginibreDrivenMaximalValue n α N z T-ginibreDrivenMaximalValue n α M z T‖ < ε := by
  let X := ginibreDrivenMaximalPath n α N z
  have hX := ginibreDrivenMaximalPath_segment T hT
  let K := X '' Icc 0 (T : ℝ)
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hX.1
  have hcf : ∀ y ∈ K, CollisionFree y := by
    rintro y ⟨t, ht, rfl⟩
    exact (hX.2.2 t ht).1
  obtain ⟨r, hr, L, g, hKt, hKtfree, hg, he⟩ := ginibreLangevinDrift_compact_tube n α K hK hcf
  let E := Real.exp ((L : ℝ)*(T : ℝ))
  have hE : 0 < E := Real.exp_pos _
  let δ := min r ε/(2*E)
  have hδ : 0 < δ := div_pos (lt_min hr hε) (by positivity)
  have hδE : δ*E = min r ε/2 := by dsimp [δ]; field_simp
  have hsmall : δ*E < r := by rw [hδE]; have hm := min_le_left r ε; linarith
  have hsmallε : δ*E < ε := by rw [hδE]; have hm := min_le_right r ε; linarith
  refine ⟨δ, hδ, ?_⟩
  intro M hM hM0 hnoise
  have hMT := ginibreDrivenMaximalLifetime_gt_of_small_noise (K := K) hn hX hM hM0
    (fun t ht => ⟨t, ht, rfl⟩) hr hKt hKtfree hg he hδ.le hsmall hnoise
  let Y := ginibreDrivenMaximalPath n α M z
  have hY := ginibreDrivenMaximalPath_segment T hMT
  have htube := ginibreDrivenSegment_stays_tube (K := K) hX hY
    (fun t ht => ⟨t, ht, rfl⟩) hr hg he hδ.le hsmall hnoise
  have hYX (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) : Y t ∈ cthickening r K := by
    apply mem_cthickening_of_dist_le _ (X t) r K ⟨t, ht, rfl⟩
    simpa only [dist_eq_norm, norm_sub_rev] using (htube t ht).le
  have hstab := ginibreDrivenSegment_noise_stability_in_extension hX hY hg he
    (fun t ht => self_subset_cthickening K ⟨t, ht, rfl⟩) hYX hδ.le hnoise
    (T : ℝ) ⟨T.property, le_rfl⟩
  have hbound := hstab.trans_lt hsmallε
  change ‖ginibreDrivenMaximalValue n α N z (Real.toNNReal (T : ℝ))-
    ginibreDrivenMaximalValue n α M z (Real.toNNReal (T : ℝ))‖ < ε at hbound
  rw [Real.toNNReal_coe] at hbound
  exact ⟨hMT, hbound⟩

end
end GinibrePoincare
