module

public import GinibrePoincare.Analysis.GinibreStochasticOUConvolution
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

@[expose] public section

/-! # A measurable path functional for the actual OU convolution -/
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Measurable realization of the convolution on the entire coordinate-path
space, with actual Brownian paths recovered almost surely. -/
def ginibreOUConvolutionFunctional (rate t : ℝ≥0) (path : ℝ≥0 → ℝ) : ℝ :=
  limUnder atTop (fun n => ginibreBrownianOURiemannSum (fun s p => p s) rate t n path)

 theorem ginibreOUConvolutionFunctional_measurable (rate t : ℝ≥0) :
    Measurable (ginibreOUConvolutionFunctional rate t) := by
  apply StronglyMeasurable.measurable
  exact StronglyMeasurable.limUnder (fun n => by
    apply Measurable.stronglyMeasurable
    unfold ginibreBrownianOURiemannSum
    fun_prop)

 theorem ginibreOUConvolutionFunctional_ae_eq {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P)
    (rate t : ℝ≥0) :
    (fun ω => ginibreOUConvolutionFunctional rate t (fun s => B s ω)) =ᵐ[P]
      ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) 0 t := by
  filter_upwards [ginibreBrownianOURiemannSum_ae_tendsto B P hB rate t] with ω hω
  exact hω.limUnder_eq

/-- The actual future convolution, driven by the actual shifted Brownian
motion, is independent of the entire Brownian past. -/
theorem ginibreBrownianOU_shift_independent_past {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P)
    (rate s t : ℝ≥0) :
    IndepFun (ginibreBrownianOU (fun u ω => B (s + u) ω - B s ω)
      rate (Real.sqrt (rate : ℝ)) 0 t)
      (fun ω (v : Set.Iic s) => B v ω) P := by
  have h := (hB.indepFun_shift s).comp (ginibreOUConvolutionFunctional_measurable rate t)
    (measurable_id)
  exact h.congr
    (ginibreOUConvolutionFunctional_ae_eq _ P (hB.shift s) rate t) (Filter.Eventually.of_forall fun _ => rfl)

end
end GinibrePoincare
