module

public import GinibrePoincare.Analysis.GinibreDrivenPathCompactExtension

@[expose] public section

/-! # The original integral equation persists at a finite compact endpoint -/
open Set Metric Filter MeasureTheory
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

 theorem ginibreDrivenPath_compact_closed_equation (n : ℕ) (α : ℝ)
    (N X : ℝ → Configuration n) (hN : Continuous N) (T : ℝ) (hT : 0 < T)
    (hX : ContinuousOn X (Ico 0 T))
    (hInt : ∀ t ∈ Ico 0 T, IntervalIntegrable (fun u => ginibreLangevinDrift n α (X u)) volume 0 t)
    (hEq : ∀ t ∈ Ico 0 T, X t = X 0+N t+∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (X u))
    (K : Set (Configuration n)) (hK : IsCompact K) (hKcf : ∀ z ∈ K, CollisionFree z)
    (hXK : ∀ t ∈ Ico 0 T, X t ∈ K) :
    ∃ W : ℝ → Configuration n, Continuous W ∧ EqOn W X (Ico 0 T) ∧
      ∀ t ∈ Icc 0 T, CollisionFree (W t) ∧
        IntervalIntegrable (fun u => ginibreLangevinDrift n α (W u)) volume 0 t ∧
        W t = W 0+N t+∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (W u) := by
  obtain ⟨W, hW, heW, hWT, hWTcf⟩ :=
    ginibreDrivenPath_compact_continuous_extension n α N X hN T hT hX hInt hEq K hK hKcf hXK
  have hcf (t : ℝ) (ht : t ∈ Icc 0 T) : CollisionFree (W t) := by
    rcases ht.2.eq_or_lt with he | he
    · rw [he]
      exact hWTcf
    · rw [heW ⟨ht.1, he⟩]
      exact hKcf _ (hXK t ⟨ht.1, he⟩)
  have hD : ContinuousOn (fun t => ginibreLangevinDrift n α (W t)) (Icc 0 T) :=
    fun t ht => ((ginibreLangevinDrift_contDiffAt n α (W t) (hcf t ht)).continuousAt.comp
      hW.continuousAt).continuousWithinAt
  have hi (t : ℝ) (ht : t ∈ Icc 0 T) :
      IntervalIntegrable (fun u => ginibreLangevinDrift n α (W u)) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht.1]
    exact hD.mono (Icc_subset_Icc_right ht.2)
  have heOld (t : ℝ) (ht : t ∈ Ico 0 T) :
      W t = W 0+N t+∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (W u) := by
    rw [heW ht, heW ⟨le_rfl, hT⟩, hEq t ht]
    congr 1
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht.1] at hu
    dsimp only
    rw [heW ⟨hu.1, hu.2.trans_lt ht.2⟩]
  have hdu : ContinuousOn (fun t => ginibreLangevinDrift n α (W t)) (uIcc 0 T) := by
    simpa only [uIcc_of_le hT.le] using hD
  have hprim := intervalIntegral.continuousOn_primitive_interval
    (hdu.integrableOn_compact (μ := volume) isCompact_uIcc)
  have hR : ContinuousOn (fun t => W 0+N t+∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (W u)) (Icc 0 T) := by
    apply (continuous_const.add hN).continuousOn.add
    simpa only [uIcc_of_le hT.le] using hprim
  haveI : (nhdsWithin T (Ico (0 : ℝ) T)).NeBot := by
    apply mem_closure_iff_nhdsWithin_neBot.mp
    rw [closure_Ico hT.ne]
    exact ⟨hT.le, le_rfl⟩
  have hWL : Tendsto W (nhdsWithin T (Ico 0 T)) (nhds (W T)) :=
    hW.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hRL := ((hR T ⟨hT.le, le_rfl⟩).mono Ico_subset_Icc_self).tendsto
  have hWT_eq : W T = W 0+N T+∫ u in (0 : ℝ)..T, ginibreLangevinDrift n α (W u) := by
    apply tendsto_nhds_unique hWL
    apply hRL.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (heOld t ht).symm
  refine ⟨W, hW, heW, ?_⟩
  intro t ht
  refine ⟨hcf t ht, hi t ht, ?_⟩
  rcases ht.2.eq_or_lt with he | he
  · subst t
    exact hWT_eq
  · exact heOld t ⟨ht.1, he⟩

end
end GinibrePoincare
