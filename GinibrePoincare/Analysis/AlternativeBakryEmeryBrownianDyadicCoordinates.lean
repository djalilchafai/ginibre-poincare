module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianDyadicTents
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- Independent coordinates for a unit-interval Brownian series: one linear
coordinate and one coefficient for each dyadic tent. -/
abbrev BakryBrownianDyadicIndex := Option (Σ n : ℕ, Fin (2^n))
abbrev BakryBrownianDyadicSample := BakryBrownianDyadicIndex → ℝ

def bakryBrownianDyadicMeasure : Measure BakryBrownianDyadicSample :=
  Measure.infinitePi (fun _ => gaussianReal 0 1)

instance : IsProbabilityMeasure bakryBrownianDyadicMeasure := by
  unfold bakryBrownianDyadicMeasure
  infer_instance

theorem bakryBrownianDyadic_coordinate_law (i : BakryBrownianDyadicIndex) :
    HasLaw (fun ω : BakryBrownianDyadicSample => ω i) (gaussianReal 0 1) bakryBrownianDyadicMeasure := by
  exact ⟨(measurable_pi_apply i).aemeasurable, Measure.infinitePi_map_eval _ i⟩

theorem bakryBrownianDyadic_coordinates_independent :
    iIndepFun (fun i (ω : BakryBrownianDyadicSample) => ω i) bakryBrownianDyadicMeasure :=
  iIndepFun_infinitePi (fun _ => measurable_id)

/-- The actual Gaussian fourth moment is finite; no numerical moment value
is needed for the uniform-series convergence argument. -/
theorem bakryBrownianDyadic_coordinate_fourth_integrable (i : BakryBrownianDyadicIndex) :
    Integrable (fun ω : BakryBrownianDyadicSample => |ω i|^4) bakryBrownianDyadicMeasure := by
  have h := ((memLp_id_gaussianReal (μ := 0) (v := 1) (4 : ℝ≥0)).integrable_norm_pow
    (p := 4) (by decide))
  simpa only [Real.norm_eq_abs, id_eq, Function.comp_def] using
    (bakryBrownianDyadic_coordinate_law i).integrable_comp h

#print axioms bakryBrownianDyadic_coordinate_law
#print axioms bakryBrownianDyadic_coordinates_independent
#print axioms bakryBrownianDyadic_coordinate_fourth_integrable
end
end GinibrePoincare
