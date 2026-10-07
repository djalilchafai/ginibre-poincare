module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralBaseMartingale

@[expose] public section

/-! Actual continuous frozen-coefficient Brownian step processes. -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def brownianFrozenStep {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (F : Ω → ℝ)
    (a b t : ℝ≥0) (ω : Ω) : ℝ := F ω*(B (max a (min t b)) ω-B a ω)

theorem brownianFrozenStep_stronglyAdapted {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (j : ι) (F : Ω → ℝ) (a b : ℝ≥0)
    (hF : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB a) _ F) :
    StronglyAdapted (ginibreBrownianAugmentedFiltration B P hB) (brownianFrozenStep (B j) F a b) := by
  intro t
  by_cases hat : a ≤ t
  · have hclamp : max a (min t b) ≤ t := max_le hat (min_le_left _ _)
    exact ((hF.mono ((ginibreBrownianAugmentedFiltration B P hB).mono hat) le_rfl).mul
      ((ginibreBrownian_augmented_coordinate_measurable_at B P hB t _ hclamp j).sub
        (ginibreBrownian_augmented_coordinate_measurable_at B P hB t a hat j))).stronglyMeasurable
  · have hta : t ≤ a := (le_of_not_ge hat)
    have hz : brownianFrozenStep (B j) F a b t = fun _ => 0 := by
      funext ω
      simp only [brownianFrozenStep, max_eq_left ((min_le_left _ _).trans hta),sub_self,mul_zero]
    rw [hz]
    exact stronglyMeasurable_const

theorem brownianFrozenStep_memLp_two {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : Ω → ℝ) (a b t : ℝ≥0)
    (hF : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB a) _ F)
    (hFi : MemLp F 2 P) : MemLp (brownianFrozenStep (B j) F a b t) 2 P := by
  have ha : a ≤ max a (min t b) := le_max_left _ _
  have hh := ginibreBrownian_augmented_linear_memLp_two B P hB hind a (max a (min t b)-a) j F hF hFi
  change MemLp (fun ω => F ω*(B j (max a (min t b)) ω-B j a ω)) 2 P
  simpa only [add_tsub_cancel_of_le ha] using hh

theorem brownianFrozenStep_continuous {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (F : Ω → ℝ) (a b : ℝ≥0) (ω : Ω) (hB : Continuous (fun t => B t ω)) :
    Continuous (fun t => brownianFrozenStep B F a b t ω) := by
  exact continuous_const.mul ((hB.comp (continuous_const.max (continuous_id.min continuous_const))).sub continuous_const)

end
end GinibrePoincare
