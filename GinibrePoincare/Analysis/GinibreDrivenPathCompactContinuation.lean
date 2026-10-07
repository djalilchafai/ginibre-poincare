module

public import GinibrePoincare.Analysis.GinibreDrivenPathRestart

@[expose] public section

/-! # Finite-time limits under the actual compact noncollision criterion -/
open Set Metric Filter MeasureTheory
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

 theorem ginibreDrivenPath_compact_collision_free_limit (n : ℕ) (α : ℝ)
    (N X : ℝ → Configuration n) (hN : Continuous N) (T : ℝ) (hT : 0 < T)
    (hX : ContinuousOn X (Ico 0 T))
    (hInt : ∀ t ∈ Ico 0 T, IntervalIntegrable (fun u => ginibreLangevinDrift n α (X u)) volume 0 t)
    (hEq : ∀ t ∈ Ico 0 T, X t = X 0+N t+∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (X u))
    (K : Set (Configuration n)) (hK : IsCompact K) (hKcf : ∀ z ∈ K, CollisionFree z)
    (hXK : ∀ t ∈ Ico 0 T, X t ∈ K) :
    ∃ z ∈ K, CollisionFree z ∧ Tendsto X (nhdsWithin T (Iio T)) (nhds z) := by
  have hb : ContinuousOn (ginibreLangevinDrift n α) K :=
    fun z hz => (ginibreLangevinDrift_contDiffAt n α z (hKcf z hz)).continuousAt.continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hb
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (X 0) (hXK 0 ⟨le_rfl, hT⟩))
  let L : ℝ≥0 := ⟨C, hC0⟩
  have hD : ContinuousOn (fun t => ginibreLangevinDrift n α (X t)) (Ico 0 T) := hb.comp hX hXK
  have hDo : ContinuousOn (fun t => ginibreLangevinDrift n α (X t)) (Ioo 0 T) :=
    hD.mono Ioo_subset_Ico_self
  have hDeriv (t : ℝ) (ht : t ∈ Ioo 0 T) :
      HasDerivAt (fun u => X u-N u) (ginibreLangevinDrift n α (X t)) t := by
    have hd := (intervalIntegral.integral_hasDerivAt_right (hInt t ⟨ht.1.le, ht.2⟩)
      (hDo.stronglyMeasurableAtFilter isOpen_Ioo t ht)
      (hDo.continuousAt (Ioo_mem_nhds ht.1 ht.2))).const_add (X 0)
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    rw [hEq u ⟨hu.1.le, hu.2⟩]
    abel
  have hLip : LipschitzOnWith L (fun u => X u-N u) (Ioo 0 T) :=
    (convex_Ioo (0 : ℝ) T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t ht => (hDeriv t ht).hasDerivWithinAt)
      (fun t ht => by exact_mod_cast hC (X t) (hXK t ⟨ht.1.le, ht.2⟩))
  obtain ⟨Y, hY, heY⟩ := hLip.extend_finite_dimension
  have hlim : Tendsto (fun t => Y t+N t) (nhdsWithin T (Iio T)) (nhds (Y T+N T)) :=
    ((hY.continuous.add hN).continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hevent : X =ᶠ[nhdsWithin T (Iio T)] (fun t => Y t+N t) := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hT)] with t ht h0
    have he := heY ⟨h0, ht⟩
    have h := congrArg (fun w => w+N t) he
    simpa only [sub_add_cancel] using h
  have hlimX : Tendsto X (nhdsWithin T (Iio T)) (nhds (Y T+N T)) := hlim.congr' hevent.symm
  have hm : Y T+N T ∈ K := hK.isClosed.mem_of_tendsto hlimX (by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hT)] with t ht h0
    exact hXK t ⟨h0.le, ht⟩)
  exact ⟨Y T+N T, hm, hKcf _ hm, hlimX⟩

end
end GinibrePoincare
