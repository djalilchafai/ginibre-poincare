module

public import GinibrePoincare.Analysis.GinibreStochasticIndependentBlocks
public import GinibrePoincare.Analysis.GinibreStochasticOUStep

@[expose] public section

/-! # Joint planar innovations independent of the entire joint Brownian past -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem ginibreBrownianOU_innovation_past_block {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P)
    (rate s t : ℝ≥0) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ × (Set.Iic s → ℝ), Measurable F ∧
      (fun ω => F (fun u => B u ω)) =ᵐ[P]
        (fun ω => (ginibreBrownianOUInnovation B rate s t ω, fun v => B v ω)) := by
  refine ⟨fun p => (ginibreOUConvolutionFunctional rate t (fun u => p (s + u) - p s),
      fun v => p v), ?_, ?_⟩
  · apply Measurable.prodMk
    · exact (ginibreOUConvolutionFunctional_measurable rate t).comp (by fun_prop)
    · fun_prop
  · filter_upwards [ginibreOUConvolutionFunctional_ae_eq _ P (hB.shift s) rate t] with ω hω
    exact congrArg (fun y => (y, fun v : Set.Iic s => B v ω)) hω

 theorem ginibreBrownianOU_planar_innovations_independent_past {Ω : Type*}
    [MeasurableSpace Ω] (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (hind : IndepFun (fun ω => fun u => Br u ω) (fun ω => fun u => Bi u ω) P)
    (rate s t : ℝ≥0) :
    IndepFun (fun ω => (ginibreBrownianOUInnovation Br rate s t ω,
        ginibreBrownianOUInnovation Bi rate s t ω))
      (fun ω => ((fun v : Set.Iic s => Br v ω), (fun v : Set.Iic s => Bi v ω))) P := by
  letI : IsProbabilityMeasure P := hBr.isGaussianProcess.isProbabilityMeasure
  obtain ⟨Fr, hFr, hr⟩ := ginibreBrownianOU_innovation_past_block Br P hBr rate s t
  obtain ⟨Fi, hFi, hi⟩ := ginibreBrownianOU_innovation_past_block Bi P hBi rate s t
  have hblocks := (hind.comp hFr hFi).congr hr hi
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
  have hrPast : HasLaw (fun ω (v : Set.Iic s) => Br v ω)
      (P.map (fun ω (v : Set.Iic s) => Br v ω)) P := ⟨hmBr.aemeasurable, rfl⟩
  have hiPast : HasLaw (fun ω (v : Set.Iic s) => Bi v ω)
      (P.map (fun ω (v : Set.Iic s) => Bi v ω)) P := ⟨hmBi.aemeasurable, rfl⟩
  exact ginibre_independent_blocks_recombine P
    (ginibreBrownianOUInnovation_hasLaw Br P hBr rate s t) hrPast
    (ginibreBrownianOUInnovation_hasLaw Bi P hBi rate s t) hiPast
    (ginibreBrownianOUInnovation_independent_past Br P hBr rate s t)
    (ginibreBrownianOUInnovation_independent_past Bi P hBi rate s t) hblocks

 theorem ginibreBrownianOU_planar_innovations_hasLaw {Ω : Type*}
    [MeasurableSpace Ω] (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (hind : IndepFun (fun ω => fun u => Br u ω) (fun ω => fun u => Bi u ω) P)
    (rate s t : ℝ≥0) :
    HasLaw (fun ω => (ginibreBrownianOUInnovation Br rate s t ω,
        ginibreBrownianOUInnovation Bi rate s t ω))
      ((gaussianReal 0 (ginibreOUVariance rate t)).prod
        (gaussianReal 0 (ginibreOUVariance rate t))) P := by
  let := hBr.isGaussianProcess.isProbabilityMeasure
  obtain ⟨Fr, hFr, hr⟩ := ginibreBrownianOU_innovation_past_block Br P hBr rate s t
  obtain ⟨Fi, hFi, hi⟩ := ginibreBrownianOU_innovation_past_block Bi P hBi rate s t
  have hblocks := (hind.comp hFr hFi).congr hr hi
  have h := hblocks.comp measurable_fst measurable_fst
  exact h.hasLaw_prod (ginibreBrownianOUInnovation_hasLaw Br P hBr rate s t)
    (ginibreBrownianOUInnovation_hasLaw Bi P hBi rate s t)

end
end GinibrePoincare
