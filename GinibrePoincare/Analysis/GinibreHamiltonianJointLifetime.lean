module

public import GinibrePoincare.Analysis.GinibreHamiltonianJointTube

@[expose] public section

/-! Actual maximal lifetime persists under uniform perturbations of the past noise. -/
open Set Metric MeasureTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

 theorem ginibreDrivenMaximalLifetime_gt_of_small_joint_perturbation {n : ℕ} (hn : 0 < n) {α : ℝ}
    {N M : ℝ → Configuration n} {z w : Configuration n} {T : ℝ≥0} {X : ℝ → Configuration n}
    (hX : GinibreDrivenSegment n α N z T X) (hM : Continuous M) (hM0 : M 0 = 0) (hw : CollisionFree w)
    {K : Set (Configuration n)} (hXK : ∀ t ∈ Icc 0 (T : ℝ), X t ∈ K)
    {r : ℝ} (hr : 0 < r) (hK : IsCompact (cthickening r K))
    (hKfree : ∀ y ∈ cthickening r K, CollisionFree y)
    {L : ℝ≥0} {g : Configuration n → Configuration n}
    (hg : LipschitzWith L g) (he : EqOn g (ginibreLangevinDrift n α) (cthickening r K))
    {δ : ℝ} (hδ : 0 ≤ δ) (hsmall : δ*Real.exp ((L : ℝ)*(T : ℝ)) < r)
    (hnoise : ∀ t ∈ Icc 0 (T : ℝ), ‖z-w‖+‖N t-M t‖ ≤ δ) :
    (T : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α M w := by
  by_contra hnT
  have hle : ginibreDrivenMaximalLifetime n α M w ≤ T := le_of_not_gt hnT
  have hfin : ginibreDrivenMaximalLifetime n α M w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hle
  have hz : CollisionFree z := by rw [← hX.2.1]; exact (hX.2.2 0 ⟨le_rfl, T.property⟩).1
  have hH : ContinuousOn (ginibreHamiltonian n) (cthickening r K) := fun y hy =>
    (ginibreHamiltonian_contDiffAt n y (hKfree y hy)).continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hH
  obtain ⟨t, ht, hBt⟩ := ginibreDrivenMaximalLifetime_finite_hamiltonian_unbounded hn α M hM hM0 w hw hfin B
  have hLT : (ginibreDrivenMaximalLifetime n α M w).toReal ≤ (T : ℝ) := by
    exact (ENNReal.toReal_le_toReal hfin ENNReal.coe_ne_top).mpr hle
  have htT : t ≤ (T : ℝ) := ht.2.le.trans hLT
  let tN : ℝ≥0 := Real.toNNReal t
  have htN : tN ≤ T := (Real.toNNReal_le_iff_le_coe).mpr htT
  have hsub : Icc (0 : ℝ) (tN : ℝ) ⊆ Icc 0 (T : ℝ) := Icc_subset_Icc_right htN
  have hXN : GinibreDrivenSegment n α N z tN X :=
    ⟨hX.1.mono hsub, hX.2.1, fun s hs => hX.2.2 s (hsub hs)⟩
  have hdomain : t ∈ ginibreDrivenMaximalDomain n α M w :=
    (ginibreDrivenMaximalDomain_eq_Ico_of_finite hfin).symm ▸ ht
  have hYN := ginibreDrivenMaximalPath_segment tN hdomain.2
  have hsmallN : δ*Real.exp ((L : ℝ)*(tN : ℝ)) < r :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left htN L.property)) hδ) hsmall
  have hst := ginibreDrivenSegment_joint_stays_tube hXN hYN (fun s hs => hXK s (hsub hs)) hr hg he hδ hsmallN
    (fun s hs => hnoise s (hsub hs)) t ⟨ht.1, by rw [Real.coe_toNNReal t ht.1]⟩
  have hmem : ginibreDrivenMaximalPath n α M w t ∈ cthickening r K := by
    apply mem_cthickening_of_dist_le _ (X t) r K (hXK t ⟨ht.1, htT⟩)
    simpa only [dist_eq_norm, norm_sub_rev] using hst.le
  have hbound := (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hB _ hmem)
  linarith


end
end GinibrePoincare
