module

public import GinibrePoincare.Analysis.GinibreHamiltonianMaximalEvaluationStability

@[expose] public section

/-! Borel measurability of the actual causal maximal solution evaluation. -/
open Set Metric MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem ginibreDrivenMaximalValue_continuousAt_alive {n : ℕ} (hn : 0 < n)
    (α : ℝ) (z : Configuration n) (T : ℝ≥0) (N : GinibreContinuousNoise n)
    (hN : (T : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N.val z) :
    ContinuousAt (fun M : GinibreContinuousNoise n => ginibreDrivenMaximalValue n α M.val z T) N := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hp⟩ := ginibreDrivenMaximalValue_uniform_noise_continuity hn α N.val z T hN ε hε
  have hc : Continuous (fun M : GinibreContinuousNoise n =>
      ‖N.val.restrict (Icc 0 (T : ℝ))-M.val.restrict (Icc 0 (T : ℝ))‖) :=
    (continuous_const.sub ((ContinuousMap.continuous_restrict _).comp continuous_subtype_val)).norm
  have hev : ∀ᶠ M in 𝓝 N,
      ‖N.val.restrict (Icc 0 (T : ℝ))-M.val.restrict (Icc 0 (T : ℝ))‖ < δ := by
    exact (hc.continuousAt (x := N)).eventually (Iio_mem_nhds (by
      simpa only [sub_self, norm_zero] using hδ))
  filter_upwards [hev] with M hM
  have hb := hp M.val M.val.continuous M.property (fun t ht =>
    (ContinuousMap.norm_coe_le_norm
      (N.val.restrict (Icc 0 (T : ℝ))-M.val.restrict (Icc 0 (T : ℝ))) ⟨t, ht⟩).trans hM.le)
  simpa only [dist_eq_norm, norm_sub_rev] using hb.2

 theorem ginibreDrivenMaximalValue_measurable {n : ℕ} (hn : 0 < n)
    (α : ℝ) (z : Configuration n) (T : ℝ≥0) :
    Measurable (fun N : GinibreContinuousNoise n => ginibreDrivenMaximalValue n α N.val z T) := by
  classical
  let s : Set (GinibreContinuousNoise n) :=
    {N | (T : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N.val z}
  let f : GinibreContinuousNoise n → Configuration n := fun N => ginibreDrivenMaximalValue n α N.val z T
  have hc : ContinuousOn f s := fun N hN =>
    (ginibreDrivenMaximalValue_continuousAt_alive hn α z T N hN).continuousWithinAt
  have hm := hc.measurable_piecewise (continuousOn_const (c := z))
    (ginibreDrivenMaximalLifetime_alive_isOpen hn α z T).measurableSet
  have he : s.piecewise f (fun _ => z) = f := by
    funext N
    by_cases hN : N ∈ s
    · simp only [Set.piecewise_eq_of_mem s f _ hN]
    · rw [Set.piecewise_eq_of_notMem s f _ hN]
      exact (dif_neg hN : ginibreDrivenMaximalValue n α N.val z T = z).symm
  rw [he] at hm
  exact hm

end
end GinibrePoincare
