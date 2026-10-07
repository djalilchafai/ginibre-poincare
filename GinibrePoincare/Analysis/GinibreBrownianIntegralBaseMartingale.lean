module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralConditional
public import GinibrePoincare.Analysis.GinibreStochasticBrownianFamilyMartingale

@[expose] public section

/-! Actual coordinate Brownian martingales in their completed joint filtration. -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem ginibreBrownian_augmented_coordinate_martingale {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (i : ι) : Martingale (B i) (ginibreBrownianAugmentedFiltration B P hB) P := by
  have hAdapt : StronglyAdapted (ginibreBrownianAugmentedFiltration B P hB) (B i) :=
    fun t => (ginibreBrownian_augmented_coordinate_measurable_at B P hB t t le_rfl i).stronglyMeasurable
  refine ⟨hAdapt, ?_⟩
  intro s t hst
  have hs : Integrable (B i s) P := ((hB i).isGaussianProcess.hasGaussianLaw_eval s).memLp_two.integrable (by norm_num)
  have ht : Integrable (B i t) P := ((hB i).isGaussianProcess.hasGaussianLaw_eval t).memLp_two.integrable (by norm_num)
  have hCs := condExp_of_stronglyMeasurable ((ginibreBrownianAugmentedFiltration B P hB).le s) (hAdapt s) hs
  have hSub := condExp_sub ht hs (ginibreBrownianAugmentedFiltration B P hB s)
  rw [hCs] at hSub
  simp only [Pi.sub_def] at hSub
  have hZero := ginibreBrownian_augmented_increment_condExp_zero B P hB hind s (t-s) i
  simp only [add_tsub_cancel_of_le hst] at hZero
  filter_upwards [hSub,hZero] with ω hω hz
  change _ = 0 at hz
  linarith

end
end GinibrePoincare
