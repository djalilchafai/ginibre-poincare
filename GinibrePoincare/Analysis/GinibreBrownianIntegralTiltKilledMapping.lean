module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralTiltOUSurvival

@[expose] public section

open MeasureTheory Set
open scoped ENNReal
namespace GinibrePoincare
noncomputable section

/-- Measurable-mapping reduction for an actual killed coupling. Restricting
the tilted measure to literal survival and pushing the coupled original path
produces precisely the reference path weighted by the terminal action on
survival. No stochastic law or survival identity is supplied by this lemma. -/
theorem actualTiltedKilledPath_map {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (d e : Ω → ℝ≥0∞) (S : Set Ω) (hS : MeasurableSet S)
    (X Y : Ω → E)
    (hXY : ∀ᵐ ω ∂P.withDensity d, ω∈S → X ω=Y ω)
    (hde : ∀ᵐ ω ∂P, ω∈S → d ω=e ω) :
    ((P.withDensity d).restrict S).map X=(P.withDensity (S.indicator e)).map Y := by
  have hPath : X=ᵐ[(P.withDensity d).restrict S] Y :=
    (ae_restrict_iff' hS).mpr hXY
  rw [Measure.map_congr hPath,restrict_withDensity hS,← withDensity_indicator hS]
  have hDensity : S.indicator d=ᵐ[P] S.indicator e := by
    filter_upwards [hde] with ω hω
    by_cases hmem : ω∈S
    · simp only [indicator_of_mem hmem]
      exact hω hmem
    · simp only [indicator_of_notMem hmem]
  rw [withDensity_congr_ae hDensity]

#print axioms actualTiltedKilledPath_map
end
end GinibrePoincare
