module

public import GinibrePoincare.Analysis.StrongConvexQuantileTransport
public import Mathlib.Probability.CDF

@[expose] public section

open MeasureTheory ProbabilityTheory Set
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Quantile transport pushes the actual source probability measure to the
actual target probability measure; its equality is proved on half-lines. -/
theorem cdfQuantileTransport_map (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hFm : StrictMono (cdf μ)) (hFr : cdf μ '' univ = Ioo 0 1)
    (hm : StrictMonoOn (cdf ν) (Ioi 0)) (hr : cdf ν '' Ioi 0 = Ioo 0 1)
    (hzero : ∀ y, y ≤ 0 → cdf ν y = 0)
    (hT : Measurable (cdfQuantileTransport (cdf μ) (cdf ν) hm hr)) :
    μ.map (cdfQuantileTransport (cdf μ) (cdf ν) hm hr) = ν := by
  let T := cdfQuantileTransport (cdf μ) (cdf ν) hm hr
  letI : IsProbabilityMeasure (μ.map T) := by infer_instance
  apply Measure.ext_of_Iic
  intro y
  rw [Measure.map_apply hT measurableSet_Iic]
  by_cases hy : 0 < y
  · have hyF : cdf ν y ∈ Ioo (0 : ℝ) 1 := hr ▸ mem_image_of_mem (cdf ν) hy
    let b := increasingCDFQuantileOn (cdf μ) univ (hFm.strictMonoOn univ) hFr (cdf ν y)
    have hb : cdf μ b = cdf ν y := increasingCDFQuantileOn_right_inverse
      (cdf μ) univ (hFm.strictMonoOn univ) hFr (cdf ν y) hyF
    have hpre : T ⁻¹' Iic y = Iic b := by
      ext x
      have hx : cdf μ x ∈ Ioo (0 : ℝ) 1 := hFr ▸ mem_image_of_mem (cdf μ) (mem_univ x)
      have hTx : 0 < T x := increasingCDFQuantileOn_mem (cdf ν) (Ioi 0) hm hr (cdf μ x) hx
      have hGT : cdf ν (T x) = cdf μ x :=
        increasingCDFQuantileOn_right_inverse (cdf ν) (Ioi 0) hm hr (cdf μ x) hx
      change T x ≤ y ↔ x ≤ b
      constructor
      · intro h
        have hFx : cdf μ x ≤ cdf μ b := by
          rw [hb, ← hGT]
          exact hm.monotoneOn hTx hy h
        exact hFm.le_iff_le.mp hFx
      · intro h
        have hFx : cdf μ x ≤ cdf ν y := by rw [← hb]; exact hFm.monotone h
        by_contra hn
        have hh := hm hy hTx (lt_of_not_ge hn)
        rw [hGT] at hh
        exact (not_lt_of_ge hFx) hh
    rw [hpre, ← ofReal_cdf μ b, hb, ofReal_cdf ν y]
  · have hpre : T ⁻¹' Iic y = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hxF : cdf μ x ∈ Ioo (0 : ℝ) 1 := hFr ▸ mem_image_of_mem (cdf μ) (mem_univ x)
      have hTx : 0 < T x := increasingCDFQuantileOn_mem (cdf ν) (Ioi 0) hm hr (cdf μ x) hxF
      exact (not_le_of_gt (lt_of_le_of_lt (le_of_not_gt hy) hTx)) hx
    rw [hpre, measure_empty, ← ofReal_cdf ν y, hzero y (le_of_not_gt hy)]
    simp

#print axioms cdfQuantileTransport_map
end
end GinibrePoincare
