module

public import Mathlib.Probability.HasLaw
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

open MeasureTheory ProbabilityTheory
namespace GinibrePoincare
noncomputable section

/-- A measurable transformation chosen from independent past data preserves
both the fresh law and independence whenever each chosen transformation
preserves that law. This is the exact finite-step innovation identity. -/
theorem independent_past_measure_transform {Ω A E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace E]
    (P : Measure Ω) [IsFiniteMeasure P] (ν : Measure A) (μ : Measure E)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]
    (Y : Ω → A) (X : Ω → E) (hY : HasLaw Y ν P) (hX : HasLaw X μ P)
    (hi : IndepFun Y X P) (T : A → E → E)
    (hT : Measurable (Function.uncurry T))
    (hpres : ∀ a, MeasurePreserving (T a) μ μ) :
    HasLaw (fun ω => T (Y ω) (X ω)) μ P ∧
      IndepFun Y (fun ω => T (Y ω) (X ω)) P := by
  have hp := (MeasurePreserving.id ν).skew_product hT
    (Filter.Eventually.of_forall (fun a => (hpres a).map_eq))
  have hj := hp.comp_hasLaw (hi.hasLaw_prod hY hX)
  have ht : HasLaw (fun ω => T (Y ω) (X ω)) μ P := by
    exact (measurePreserving_snd (μ := ν) (ν := μ)).comp_hasLaw hj
  refine ⟨ht, (indepFun_iff_hasLaw_prodMk_prod hY ht).mpr ?_⟩
  exact hj

end
end GinibrePoincare
