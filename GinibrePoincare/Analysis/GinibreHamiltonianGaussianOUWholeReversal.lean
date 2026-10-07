module

public import GinibrePoincare.Analysis.GinibreHamiltonianGaussianOUFiniteLaw
public import GinibrePoincare.Analysis.BrownianOrthogonalPathLaw

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem ginibreBrownianOU_stationary_whole_horizon_law_reversal
    {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : IsBrownianReal B P) (Z : Ω → ℝ) (hZ : HasLaw Z (gaussianReal 0 (1/2)) P)
    (hind : IndepFun Z (fun ω t => B t ω) P) (rate T : ℝ≥0) :
    P.map (fun ω => fun t : Icc (0 : ℝ≥0) T =>
      ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) (Z ω) t.val ω) =
    P.map (fun ω => fun t : Icc (0 : ℝ≥0) T =>
      ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) (Z ω) ((T-t.val : ℝ≥0) : ℝ) ω) := by
  classical
  let X : Ω → Icc (0 : ℝ≥0) T → ℝ := fun ω t =>
    ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) (Z ω) t.val ω
  let Y : Ω → Icc (0 : ℝ≥0) T → ℝ := fun ω t =>
    ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) (Z ω) ((T-t.val : ℝ≥0) : ℝ) ω
  have hG := ginibreBrownianOU_gaussian_initial_isGaussianProcess P B hB Z hZ.hasGaussianLaw hind rate
  have hmX : Measurable X := Measurable.of_eval (fun t =>
    aemeasurable_iff_measurable.mp (hG.aemeasurable t.val))
  have hmY : Measurable Y := Measurable.of_eval (fun t =>
    aemeasurable_iff_measurable.mp (hG.aemeasurable (T-t.val)))
  let μ (I : Finset (Icc (0 : ℝ≥0) T)) : Measure (I → ℝ) :=
    P.map (fun ω => I.restrict (X ω))
  have hx : IsProjectiveLimit (P.map X) μ := by
    intro I
    rw [Measure.map_map (show Measurable I.restrict by fun_prop) hmX]
    rfl
  have hy : IsProjectiveLimit (P.map Y) μ := by
    intro I
    rw [Measure.map_map (show Measurable I.restrict by fun_prop) hmY]
    have he := ginibreBrownianOU_stationary_finite_law_reversal B P hB Z hZ hind rate T
      (fun i : I => i.val.val) (fun i => i.val.property.2)
    let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => ℝ)
    have he' := congrArg (fun ν : Measure (EuclideanSpace ℝ I) => ν.map e) he
    rw [Measure.map_map e.continuous.measurable
      (show Measurable (fun ω => WithLp.toLp 2 (fun i : I => X ω i.val)) from
        (PiLp.continuous_toLp 2 _).measurable.comp (Measurable.of_eval (fun i => (measurable_pi_apply i.val).comp hmX))),
      Measure.map_map e.continuous.measurable
      (show Measurable (fun ω => WithLp.toLp 2 (fun i : I => Y ω i.val)) from
        (PiLp.continuous_toLp 2 _).measurable.comp (Measurable.of_eval (fun i => (measurable_pi_apply i.val).comp hmY)))] at he'
    exact he'.symm
  exact hx.unique hy

end
end GinibrePoincare
