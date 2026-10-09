module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralFrozenStep

@[expose] public section

/-! Conditional identification of the actual frozen Brownian step with its terminal value. -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem brownianFrozenStep_conditional_terminal {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : Ω → ℝ) (a b t : ℝ≥0) (hab : a ≤ b)
    (hF : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB a) _ F)
    (hFi : MemLp F 2 P) :
    P[(fun ω => F ω*(B j b ω-B j a ω)) | ginibreBrownianAugmentedFiltration B P hB t] =ᵐ[P]
      brownianFrozenStep (B j) F a b t := by
  let ℱ := ginibreBrownianAugmentedFiltration B P hB
  let L := fun ω => F ω*(B j b ω-B j a ω)
  have hL : MemLp L 2 P := by
    have hh := ginibreBrownian_augmented_linear_memLp_two B P hB hind a (b-a) j F hF hFi
    simpa only [add_tsub_cancel_of_le hab] using hh
  by_cases hta : t ≤ a
  · have hz : P[L | ℱ a] =ᵐ[P] (fun _ => 0) := by
      simpa only [add_tsub_cancel_of_le hab] using
        ginibreBrownian_augmented_linear_condExp_zero B P hB hind a (b-a) j F hF hFi
    have htower := condExp_condExp_of_le (ℱ.mono hta) (ℱ.le a) (f := L) (μ := P)
    have hzero : P[L | ℱ t] =ᵐ[P] (fun _ => 0) := by
      apply htower.symm.trans
      apply (condExp_congr_ae hz).trans
      exact EventuallyEq.of_eq (condExp_zero)
    have hs : brownianFrozenStep (B j) F a b t = fun _ => 0 := by
      funext ω
      simp only [brownianFrozenStep, max_eq_left ((min_le_left _ _).trans hta), sub_self, mul_zero]
    simpa only [hs] using hzero
  · have hat : a ≤ t := le_of_not_ge hta
    by_cases hbt : b ≤ t
    · have hLM : @Measurable Ω ℝ (ℱ t) _ L :=
        ((hF.mono (ℱ.mono (hab.trans hbt)) le_rfl).mul
          ((ginibreBrownian_augmented_coordinate_measurable_at B P hB t b hbt j).sub
            (ginibreBrownian_augmented_coordinate_measurable_at B P hB t a (hab.trans hbt) j)))
      have hh := condExp_of_stronglyMeasurable (ℱ.le t) hLM.stronglyMeasurable (hL.integrable (by norm_num))
      apply Eventually.of_forall
      intro ω
      change P[L | ℱ t] ω = _
      rw [hh]
      simp only [L, brownianFrozenStep, min_eq_right hbt, max_eq_right hab]
    · have htb : t ≤ b := le_of_not_ge hbt
      let A := fun ω => F ω*(B j b ω-B j t ω)
      let C := fun ω => F ω*(B j t ω-B j a ω)
      have hFt : @Measurable Ω ℝ (ℱ t) _ F := hF.mono (ℱ.mono hat) le_rfl
      have hA : MemLp A 2 P := by
        have hh := ginibreBrownian_augmented_linear_memLp_two B P hB hind t (b-t) j F hFt hFi
        simpa only [add_tsub_cancel_of_le htb] using hh
      have hC : MemLp C 2 P := by
        have hh := ginibreBrownian_augmented_linear_memLp_two B P hB hind a (t-a) j F hF hFi
        simpa only [add_tsub_cancel_of_le hat] using hh
      have hCM : @Measurable Ω ℝ (ℱ t) _ C := hFt.mul
        ((ginibreBrownian_augmented_coordinate_measurable_at B P hB t t le_rfl j).sub
          (ginibreBrownian_augmented_coordinate_measurable_at B P hB t a hat j))
      have hAC : L = A+C := by funext ω; dsimp [L, A, C]; ring
      have hCE := condExp_add (hA.integrable (by norm_num)) (hC.integrable (by norm_num)) (ℱ t)
      have hCC := condExp_of_stronglyMeasurable (ℱ.le t) hCM.stronglyMeasurable (hC.integrable (by norm_num))
      have hCA : P[A | ℱ t] =ᵐ[P] (fun _ => 0) := by
        simpa only [add_tsub_cancel_of_le htb] using
          ginibreBrownian_augmented_linear_condExp_zero B P hB hind t (b-t) j F hFt hFi
      change P[L | ℱ t] =ᵐ[P] _
      rw [hAC]
      apply hCE.trans
      filter_upwards [hCA] with ω hω
      simp only [Pi.add_apply, hω, hCC, zero_add, brownianFrozenStep, min_eq_left htb, max_eq_right hat]
      rfl

end
end GinibrePoincare
