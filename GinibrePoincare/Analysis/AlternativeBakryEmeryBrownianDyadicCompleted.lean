module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianDyadicUniform
public import Mathlib.MeasureTheory.Measure.NullMeasurable
@[expose] public section
open Set MeasureTheory ProbabilityTheory
namespace GinibrePoincare
noncomputable section
local instance bakryBrownianCompleted_pathMeasurable :
    MeasurableSpace C(Icc (0 : ℝ) 1, ℝ) := borel _
local instance bakryBrownianCompleted_pathBorel :
    BorelSpace C(Icc (0 : ℝ) 1, ℝ) := ⟨rfl⟩

abbrev BakryBrownianDyadicCompletedSample :=
  NullMeasurableSpace BakryBrownianDyadicSample bakryBrownianDyadicMeasure

def bakryBrownianDyadicCompletedMeasure : Measure BakryBrownianDyadicCompletedSample :=
  bakryBrownianDyadicMeasure.completion

instance : IsProbabilityMeasure bakryBrownianDyadicCompletedMeasure :=
  ⟨by change bakryBrownianDyadicMeasure univ = 1; exact measure_univ⟩

instance : bakryBrownianDyadicCompletedMeasure.IsComplete :=
  Measure.completion.isComplete _

def bakryBrownianDyadicCompletedPath (ω : BakryBrownianDyadicCompletedSample) : C(Icc (0 : ℝ) 1, ℝ) :=
  bakryBrownianDyadicPath ω

theorem bakryBrownianDyadicCompletedPath_measurable : Measurable bakryBrownianDyadicCompletedPath :=
  bakryBrownianDyadicPath_aemeasurable.nullMeasurable.measurable'

/-- Completing the actual Gaussian sample space preserves every measurable
finite-dimensional law, including the almost-everywhere series limit. -/
theorem bakryBrownianDyadic_completed_map {E : Type*} [MeasurableSpace E]
    (f : BakryBrownianDyadicSample → E) (hf : AEMeasurable f bakryBrownianDyadicMeasure) :
    bakryBrownianDyadicCompletedMeasure.map (fun ω : BakryBrownianDyadicCompletedSample => f ω) =
      bakryBrownianDyadicMeasure.map f := by
  ext s hs
  rw [Measure.map_apply hf.nullMeasurable.measurable' hs,
    Measure.map_apply_of_aemeasurable hf hs]
  rfl

#print axioms bakryBrownianDyadicCompletedPath_measurable
#print axioms bakryBrownianDyadic_completed_map
end
end GinibrePoincare
