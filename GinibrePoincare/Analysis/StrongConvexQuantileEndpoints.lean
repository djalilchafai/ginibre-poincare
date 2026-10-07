module

public import GinibrePoincare.Analysis.StrongConvexCDF

@[expose] public section

open Set Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- Positive-support quantiles tend to the left endpoint at probability zero. -/
theorem increasingCDFQuantileOn_tendsto_zero (F : ℝ → ℝ)
    (hm : StrictMonoOn F (Ici 0)) (h0 : F 0 = 0)
    (hr : F '' Ioi 0 = Ioo 0 1) :
    Tendsto (increasingCDFQuantileOn F (Ioi 0) (hm.mono Ioi_subset_Ici_self) hr)
      (𝓝[Ioo 0 1] 0) (𝓝 0) := by
  let q := increasingCDFQuantileOn F (Ioi 0) (hm.mono Ioi_subset_Ici_self) hr
  apply tendsto_order.2
  constructor
  · intro b hb
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hq := increasingCDFQuantileOn_mem F (Ioi 0) (hm.mono Ioi_subset_Ici_self) hr u hu
    exact lt_trans hb (show 0 < q u from hq)
  · intro b hb
    have hFb : 0 < F b := by
      simpa only [h0] using hm (self_mem_Ici : (0 : ℝ) ∈ Ici 0) hb.le hb
    filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds hFb), self_mem_nhdsWithin] with u hu huI
    have hq := increasingCDFQuantileOn_mem F (Ioi 0) (hm.mono Ioi_subset_Ici_self) hr u huI
    have he := increasingCDFQuantileOn_right_inverse F (Ioi 0) (hm.mono Ioi_subset_Ici_self) hr u huI
    change 0 < q u at hq
    change F (q u) = u at he
    by_contra hn
    have h := hm.monotoneOn hb.le (show 0 ≤ q u from hq.le) (le_of_not_gt hn)
    rw [he] at h
    exact (not_le_of_gt hu) h

/-- Positive-support quantiles tend to infinity at probability one. -/
theorem increasingCDFQuantileOn_tendsto_atTop (F : ℝ → ℝ)
    (hm : StrictMonoOn F (Ici 0)) (hr : F '' Ioi 0 = Ioo 0 1) :
    Tendsto (increasingCDFQuantileOn F (Ioi 0) (hm.mono Ioi_subset_Ici_self) hr)
      (𝓝[Ioo 0 1] 1) atTop := by
  let q := increasingCDFQuantileOn F (Ioi 0) (hm.mono Ioi_subset_Ici_self) hr
  apply tendsto_atTop.2
  intro b
  let B := max b 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hFB : F B < 1 := (hr ▸ Set.mem_image_of_mem F hB).2
  filter_upwards [nhdsWithin_le_nhds (eventually_gt_nhds hFB), self_mem_nhdsWithin] with u hu huI
  have hq := increasingCDFQuantileOn_mem F (Ioi 0) (hm.mono Ioi_subset_Ici_self) hr u huI
  have he := increasingCDFQuantileOn_right_inverse F (Ioi 0) (hm.mono Ioi_subset_Ici_self) hr u huI
  change 0 < q u at hq
  change F (q u) = u at he
  have hBq : B < q u := by
    change 0 < q u at hq
    change F (q u) = u at he
    by_contra hn
    have h := hm.monotoneOn (show 0 ≤ q u from hq.le) hB.le (le_of_not_gt hn)
    rw [he] at h
    exact (not_le_of_gt hu) h
  exact (le_max_left b 1).trans hBq.le

#print axioms increasingCDFQuantileOn_tendsto_zero
#print axioms increasingCDFQuantileOn_tendsto_atTop
end
end GinibrePoincare
