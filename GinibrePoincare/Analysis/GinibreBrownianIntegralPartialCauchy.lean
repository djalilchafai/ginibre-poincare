module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralPartialGeometry
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

@[expose] public section

/-! Conditional contraction makes the actual continuous partial sums L² Cauchy at every time. -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem real_condExp_square_integral_le {Ω : Type*} [mAmbient : MeasurableSpace Ω]
    (P : Measure Ω) (m : MeasurableSpace Ω) (hm : m ≤ mAmbient) [SigmaFinite (P.trim hm)]
    (f : Ω → ℝ) (hf : MemLp f 2 P) :
    (∫ ω, (P[f | m] ω)^2 ∂P) ≤ ∫ ω, (f ω)^2 ∂P := by
  have hi : Integrable (fun ω => ‖f ω‖^(2 : ℝ)) P := by
    simpa only [Real.rpow_two,Real.norm_eq_abs,sq_abs] using hf.integrable_sq
  have hle := Integrable.norm_condExp_rpow_le (f := f) (m := m) (μ := P) (p := 2) (by norm_num) hi
  have hj : (fun ω => (P[f | m] ω)^2) ≤ᵐ[P] P[(fun ω => (f ω)^2) | m] := by
    simpa only [Real.rpow_two,Real.norm_eq_abs,sq_abs] using hle
  calc
    _ ≤ ∫ ω, P[(fun ω => (f ω)^2) | m] ω ∂P :=
      integral_mono_ae ((hf.condExp (by norm_num)).integrable_sq) integrable_condExp hj
    _ = _ := integral_condExp hm

theorem brownianUniformPartialSum_memLp_two {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F t))
    (hFi : ∀ t, MemLp (F t) 2 P) (T : ℝ≥0) (N : ℕ) (t : ℝ≥0) :
    MemLp (brownianUniformPartialSum (B j) F T N t) 2 P := by
  convert! memLp_finsetSum (Finset.range N) (fun i _ =>
    brownianFrozenStep_memLp_two B P hB hind j (F (itoUniformNNTime T N i))
      (itoUniformNNTime T N i) (itoUniformNNTime T N (i+1)) t (hF _) (hFi _)) using 1

theorem brownianUniformPartialSum_difference_secondMoment_le_terminal {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F t))
    (hFi : ∀ t, MemLp (F t) 2 P) (T : ℝ≥0) (N M : ℕ) (t : ℝ≥0) (ht : t ≤ T) :
    (∫ ω, (brownianUniformPartialSum (B j) F T N t ω-brownianUniformPartialSum (B j) F T M t ω)^2 ∂P) ≤
      ∫ ω, (brownianUniformLeftSum (B j) F T N ω-brownianUniformLeftSum (B j) F T M ω)^2 ∂P := by
  have hm := (brownianUniformPartialSum_martingale B P hB hind j F hF hFi T N).sub
    (brownianUniformPartialSum_martingale B P hB hind j F hF hFi T M)
  have hc := hm.condExp_ae_eq ht
  have hf : MemLp (fun ω => brownianUniformLeftSum (B j) F T N ω-brownianUniformLeftSum (B j) F T M ω) 2 P :=
    (brownianUniformLeftSum_memLp_two B P hB hind j F hF hFi T N).sub
      (brownianUniformLeftSum_memLp_two B P hB hind j F hF hFi T M)
  have hterminal : (brownianUniformPartialSum (B j) F T N-brownianUniformPartialSum (B j) F T M) T =
      fun ω => brownianUniformLeftSum (B j) F T N ω-brownianUniformLeftSum (B j) F T M ω := by
    funext ω
    simp only [Pi.sub_apply,brownianUniformPartialSum_terminal]
  rw [hterminal] at hc
  calc
    _ = ∫ ω, (P[(fun ω => brownianUniformLeftSum (B j) F T N ω-brownianUniformLeftSum (B j) F T M ω) |
        ginibreBrownianAugmentedFiltration B P hB t] ω)^2 ∂P := by
      apply integral_congr_ae
      filter_upwards [hc] with ω hω
      simpa only [Pi.sub_apply] using congrArg (fun x : ℝ => x^2) hω.symm
    _ ≤ _ := real_condExp_square_integral_le P _ ((ginibreBrownianAugmentedFiltration B P hB).le t) _ hf

theorem brownianUniformPartialSum_tendsto_difference_meanSquare {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F t))
    (hFi : ∀ t, MemLp (F t) 2 P) (T t : ℝ≥0) (ht : t ≤ T)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun s => F s ω) (Set.Icc 0 T))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ s ∈ Set.Icc 0 T, ∀ ω, ‖F s ω‖ ≤ C) :
    Tendsto (fun q : ℕ×ℕ => ∫ ω,
      (brownianUniformPartialSum (B j) F T (q.1+1) t ω-brownianUniformPartialSum (B j) F T (q.2+1) t ω)^2 ∂P)
      atTop (𝓝 0) := by
  have hle (q : ℕ×ℕ) :
      (∫ ω, (brownianUniformPartialSum (B j) F T (q.1+1) t ω-brownianUniformPartialSum (B j) F T (q.2+1) t ω)^2 ∂P) ≤
        ∫ ω, (brownianUniformLeftSum (B j) F T (q.1+1) ω-brownianUniformLeftSum (B j) F T (q.2+1) ω)^2 ∂P :=
    brownianUniformPartialSum_difference_secondMoment_le_terminal B P hB hind j F hF hFi T _ _ t ht
  exact squeeze_zero (fun q => integral_nonneg fun ω => sq_nonneg _) hle
    (brownianUniformLeftSum_tendsto_difference_meanSquare B P hB hind j F hF hFi T hc C hC hbound)

end
end GinibrePoincare
