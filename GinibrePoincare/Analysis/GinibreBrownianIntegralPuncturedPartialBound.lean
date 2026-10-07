module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralPuncturedContinuous

@[expose] public section

/-! Initial-cutoff error control for actual partial Brownian sums, obtained
from their genuine martingale terminal contraction. -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem brownianUniformPartialSum_initial_cutoff_error_bound {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F t))
    (C ε : ℝ) (hC : 0 ≤ C) (hε : 0 < ε) (hb : ∀ t ω, ‖F t ω‖ ≤ C)
    (T t : ℝ≥0) (hT : 0 < T) (ht : t ≤ T) (N : ℕ) (hN : 0 < N) :
    (∫ ω, (brownianUniformPartialSum (B j) F T N t ω-
      brownianUniformPartialSum (B j) (brownianInitialTimeCutoff F ε) T N t ω)^2 ∂P) ≤
      C^2*(2*ε+(T : ℝ)/(N : ℝ)) := by
  let ℱ := ginibreBrownianAugmentedFiltration B P hB
  let A := brownianInitialTimeCutoff F ε
  have ha := brownianInitialTimeCutoff_adapted F ε ℱ hF
  have hFi (r : ℝ≥0) : MemLp (F r) 2 P := MemLp.of_bound
    ((hF r).mono (ℱ.le r) le_rfl).aestronglyMeasurable C (ae_of_all P (hb r))
  have hAi (r : ℝ≥0) : MemLp (A r) 2 P := MemLp.of_bound
    ((ha r).mono (ℱ.le r) le_rfl).aestronglyMeasurable C
    (ae_of_all P fun ω => brownianInitialTimeCutoff_bound F ε C hb r ω)
  have hM := brownianUniformPartialSum_martingale B P hB hind j F hF hFi T N
  have hA := brownianUniformPartialSum_martingale B P hB hind j A ha hAi T N
  have hh := realMartingale_difference_secondMoment_le_terminal P ℱ _ _ hM hA T t ht
    (brownianUniformPartialSum_memLp_two B P hB hind j F hF hFi T N T)
    (brownianUniformPartialSum_memLp_two B P hB hind j A ha hAi T N T)
  simp only [brownianUniformPartialSum_terminal] at hh
  exact hh.trans (brownianUniformLeftSum_initial_cutoff_error_bound B P hB hind j F hF
    C ε hC hε hb T hT N hN)

#print axioms brownianUniformPartialSum_initial_cutoff_error_bound
end
end GinibrePoincare
