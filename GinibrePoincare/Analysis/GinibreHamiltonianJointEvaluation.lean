module

public import GinibrePoincare.Analysis.GinibreHamiltonianJointEvaluationStability
public import GinibrePoincare.Analysis.GinibreHamiltonianMaximalEvaluation

@[expose] public section

/-! Joint initial-state/noise measurability of the genuine canonical maximal solution. -/
open Set Metric MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem ginibreDrivenMaximalValue_joint_continuousAt_alive {n : ℕ} (hn : 0 < n)
    (α : ℝ) (T : ℝ≥0)
    (p : {z : Configuration n // CollisionFree z} × GinibreContinuousNoise n)
    (hp : (T : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α p.2.val p.1.val) :
    ContinuousAt (fun q : {z : Configuration n // CollisionFree z} × GinibreContinuousNoise n =>
      ginibreDrivenMaximalValue n α q.2.val q.1.val T) p := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hstab⟩ := ginibreDrivenMaximalValue_uniform_joint_continuity hn α p.2.val p.1.val T hp ε hε
  have hc : Continuous (fun q : {z : Configuration n // CollisionFree z} × GinibreContinuousNoise n =>
      ‖p.1.val-q.1.val‖+‖p.2.val.restrict (Icc 0 (T : ℝ))-q.2.val.restrict (Icc 0 (T : ℝ))‖) :=
    (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).norm.add
      (continuous_const.sub ((ContinuousMap.continuous_restrict _).comp
        (continuous_subtype_val.comp continuous_snd))).norm
  have hev : ∀ᶠ q in 𝓝 p,
      ‖p.1.val-q.1.val‖+‖p.2.val.restrict (Icc 0 (T : ℝ))-q.2.val.restrict (Icc 0 (T : ℝ))‖ < δ :=
    (hc.continuousAt (x := p)).eventually (Iio_mem_nhds (by
      simpa only [sub_self, norm_zero, zero_add] using hδ))
  filter_upwards [hev] with q hq
  have hb := hstab q.1.val q.2.val q.1.property q.2.val.continuous q.2.property (fun t ht =>
    (add_le_add_right (ContinuousMap.norm_coe_le_norm
      (p.2.val.restrict (Icc 0 (T : ℝ))-q.2.val.restrict (Icc 0 (T : ℝ))) ⟨t, ht⟩) _).trans hq.le)
  simpa only [dist_eq_norm, norm_sub_rev] using hb.2

theorem ginibreDrivenMaximalLifetime_joint_alive_isOpen {n : ℕ} (hn : 0 < n)
    (α : ℝ) (T : ℝ≥0) :
    IsOpen {p : {z : Configuration n // CollisionFree z} × GinibreContinuousNoise n |
      (T : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α p.2.val p.1.val} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  obtain ⟨δ, hδ, hstab⟩ := ginibreDrivenMaximalValue_uniform_joint_continuity hn α p.2.val p.1.val T hp 1 zero_lt_one
  have hc : Continuous (fun q : {z : Configuration n // CollisionFree z} × GinibreContinuousNoise n =>
      ‖p.1.val-q.1.val‖+‖p.2.val.restrict (Icc 0 (T : ℝ))-q.2.val.restrict (Icc 0 (T : ℝ))‖) :=
    (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).norm.add
      (continuous_const.sub ((ContinuousMap.continuous_restrict _).comp
        (continuous_subtype_val.comp continuous_snd))).norm
  have hev : ∀ᶠ q in 𝓝 p,
      ‖p.1.val-q.1.val‖+‖p.2.val.restrict (Icc 0 (T : ℝ))-q.2.val.restrict (Icc 0 (T : ℝ))‖ < δ :=
    (hc.continuousAt (x := p)).eventually (Iio_mem_nhds (by
      simpa only [sub_self, norm_zero, zero_add] using hδ))
  filter_upwards [hev] with q hq
  exact (hstab q.1.val q.2.val q.1.property q.2.val.continuous q.2.property (fun t ht =>
    (add_le_add_right (ContinuousMap.norm_coe_le_norm
      (p.2.val.restrict (Icc 0 (T : ℝ))-q.2.val.restrict (Icc 0 (T : ℝ))) ⟨t, ht⟩) _).trans hq.le)).1

theorem ginibreDrivenMaximalValue_joint_measurable {n : ℕ} (hn : 0 < n)
    (α : ℝ) (T : ℝ≥0) :
    Measurable (fun p : {z : Configuration n // CollisionFree z} × GinibreContinuousNoise n =>
      ginibreDrivenMaximalValue n α p.2.val p.1.val T) := by
  classical
  let s : Set ({z : Configuration n // CollisionFree z} × GinibreContinuousNoise n) :=
    {p | (T : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α p.2.val p.1.val}
  let f := fun p : {z : Configuration n // CollisionFree z} × GinibreContinuousNoise n =>
    ginibreDrivenMaximalValue n α p.2.val p.1.val T
  have hc : ContinuousOn f s := fun p hp =>
    (ginibreDrivenMaximalValue_joint_continuousAt_alive hn α T p hp).continuousWithinAt
  have hm := hc.measurable_piecewise
    (continuous_subtype_val.comp continuous_fst).continuousOn
    (ginibreDrivenMaximalLifetime_joint_alive_isOpen hn α T).measurableSet
  have he : s.piecewise f (fun p => p.1.val) = f := by
    funext p
    by_cases hp : p ∈ s
    · simp only [Set.piecewise_eq_of_mem s f _ hp]
    · rw [Set.piecewise_eq_of_notMem s f _ hp]
      exact (dif_neg hp : ginibreDrivenMaximalValue n α p.2.val p.1.val T = p.1.val).symm
  change Measurable (s.piecewise f (fun p => p.1.val)) at hm
  rw [he] at hm
  exact hm

end
end GinibrePoincare
