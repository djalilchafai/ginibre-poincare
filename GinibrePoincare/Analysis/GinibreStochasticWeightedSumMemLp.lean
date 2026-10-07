module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralSubstitutionFinite
public import GinibrePoincare.Analysis.GinibreBrownianIntegralUniformSums

@[expose] public section

open MeasureTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreWeightedUniformLeftSum_memLp
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (β A : ℝ≥0 → Ω → ℝ) (hβ : ∀ t, MemLp (β t) 2 P)
    (hA : ∀ t, AEStronglyMeasurable (A t) P)
    (C : ℝ) (hb : ∀ t ω, ‖A t ω‖ ≤ C) (T : ℝ≥0) (N : ℕ) :
    MemLp (brownianUniformLeftSum β A T N) 2 P := by
  unfold brownianUniformLeftSum
  apply memLp_finsetSum
  intro i hi
  exact actualBoundedMultiplier_memLp_two P _ _ (hA _)
    ((hβ _).sub (hβ _)) C (hb _)
end
end GinibrePoincare
