module

public import GinibrePoincare.Analysis.BrownianNullAugmentationIndependence

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem brownianFamily_fresh_increment_independent_augmented_variable {Ω ι A : Type*}
    [mAmbient : MeasurableSpace Ω] [Fintype ι] [MeasurableSpace A]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (s t : ℝ≥0) (Y : Ω → A)
    (hY : @Measurable Ω A (ginibreBrownianAugmentedFiltration B P hB s) _ Y) :
    IndepFun (fun ω i => B i (s+t) ω-B i s ω) Y P := by
  have hx : Measurable (fun ω i => B i (s+t) ω-B i s ω) := by
    apply measurable_pi_lambda
    intro i
    exact (aemeasurable_iff_measurable.mp ((hB i).aemeasurable (s+t))).sub
      (aemeasurable_iff_measurable.mp ((hB i).aemeasurable s))
  apply indepFun_of_nullAugmented_measurable (mAmbient := mAmbient) P
    (ginibreBrownianFamilyPastSpace B s) (ginibreBrownianFamilyPastSpace_le B P hB s)
    _ hx Y hY
  exact ginibreBrownian_family_increment_independent_past B P hB hind s t

#print axioms brownianFamily_fresh_increment_independent_augmented_variable
end
end GinibrePoincare
