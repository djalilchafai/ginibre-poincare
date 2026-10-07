module

public import GinibrePoincare.Analysis.GinibreStochasticIndependentBlocks
public import GinibrePoincare.Analysis.GinibreStochasticBrownianQuadraticInnovation

@[expose] public section

/-! Actual planar Brownian increments are independent of the entire joint past. -/
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem ginibreBrownian_planar_increment_independent_past {Ω : Type*}
    [MeasurableSpace Ω] (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (hind : IndepFun (fun ω u => Br u ω) (fun ω u => Bi u ω) P) (s t : ℝ≥0) :
    IndepFun (fun ω => (Br (s+t) ω-Br s ω, Bi (s+t) ω-Bi s ω))
      (fun ω => ((fun v : Set.Iic s => Br v ω), (fun v : Set.Iic s => Bi v ω))) P := by
  let := hBr.isGaussianProcess.isProbabilityMeasure
  let F : (ℝ≥0 → ℝ) → ℝ × (Set.Iic s → ℝ) := fun p => (p (s+t)-p s, fun v => p v)
  have hmF : Measurable F := by fun_prop
  have hblocks := hind.comp hmF hmF
  have hmBr : Measurable (fun ω (v : Set.Iic s) => Br v ω) := by
    apply measurable_pi_lambda
    intro v
    exact aemeasurable_iff_measurable.mp (hBr.aemeasurable v)
  have hmBi : Measurable (fun ω (v : Set.Iic s) => Bi v ω) := by
    apply measurable_pi_lambda
    intro v
    exact aemeasurable_iff_measurable.mp (hBi.aemeasurable v)
  letI : IsProbabilityMeasure (P.map (fun ω (v : Set.Iic s) => Br v ω)) := by infer_instance
  letI : IsProbabilityMeasure (P.map (fun ω (v : Set.Iic s) => Bi v ω)) := by infer_instance
  have hr : HasLaw (fun ω => Br (s+t) ω-Br s ω) (gaussianReal 0 t) P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw Br P hBr.toIsPreBrownianReal s (s+t)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le))
  have hi : HasLaw (fun ω => Bi (s+t) ω-Bi s ω) (gaussianReal 0 t) P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw Bi P hBi.toIsPreBrownianReal s (s+t)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le))
  exact ginibre_independent_blocks_recombine P hr ⟨hmBr.aemeasurable,rfl⟩ hi ⟨hmBi.aemeasurable,rfl⟩
    (ginibreBrownian_increment_whole_past_independent Br P hBr.toIsPreBrownianReal s t)
    (ginibreBrownian_increment_whole_past_independent Bi P hBi.toIsPreBrownianReal s t) hblocks

theorem ginibreBrownian_planar_increment_hasLaw {Ω : Type*}
    [MeasurableSpace Ω] (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (hind : IndepFun (fun ω u => Br u ω) (fun ω u => Bi u ω) P) (s t : ℝ≥0) :
    HasLaw (fun ω => (Br (s+t) ω-Br s ω, Bi (s+t) ω-Bi s ω))
      ((gaussianReal 0 t).prod (gaussianReal 0 t)) P := by
  let := hBr.isGaussianProcess.isProbabilityMeasure
  have hm : Measurable (fun p : ℝ≥0 → ℝ => p (s+t)-p s) := by fun_prop
  apply (hind.comp hm hm).hasLaw_prod
  · change HasLaw (fun ω => Br (s+t) ω-Br s ω) (gaussianReal 0 t) P
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw Br P hBr.toIsPreBrownianReal s (s+t)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le))
  · change HasLaw (fun ω => Bi (s+t) ω-Bi s ω) (gaussianReal 0 t) P
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw Bi P hBi.toIsPreBrownianReal s (s+t)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from bot_le))

end
end GinibrePoincare
