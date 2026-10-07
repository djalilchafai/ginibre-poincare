module

public import Mathlib.Probability.Kernel.CondDistrib
public import Mathlib.Probability.HasLaw

@[expose] public section

/-! # Conditional probability kernel of a genuine independent innovation -/
open MeasureTheory ProbabilityTheory
open scoped MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem ginibreIndependent_condDistrib {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P] (R : Ω → β) (Z : Ω → ℝ)
    (hR : Measurable R) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hZ : HasLaw Z ν P) (hind : IndepFun Z R P) :
    condDistrib Z R P =ᵐ[P.map R] Kernel.const β ν := by
  apply condDistrib_ae_eq_of_measure_eq_compProd hR.aemeasurable hZ.aemeasurable
  rw [Measure.compProd_const]
  rw [hind.symm.map_prod_eq_prod_map_map hR.aemeasurable hZ.aemeasurable, hZ.map_eq]

 theorem ginibreIndependent_condDistrib_general {Ω β ζ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace β] [MeasurableSpace ζ]
    [StandardBorelSpace ζ] [Nonempty ζ]
    (P : Measure Ω) [IsProbabilityMeasure P] (R : Ω → β) (Z : Ω → ζ)
    (hR : Measurable R) (ν : Measure ζ) [IsProbabilityMeasure ν]
    (hZ : HasLaw Z ν P) (hind : IndepFun Z R P) :
    condDistrib Z R P =ᵐ[P.map R] Kernel.const β ν := by
  apply condDistrib_ae_eq_of_measure_eq_compProd hR.aemeasurable hZ.aemeasurable
  rw [Measure.compProd_const]
  rw [hind.symm.map_prod_eq_prod_map_map hR.aemeasurable hZ.aemeasurable, hZ.map_eq]

end
end GinibrePoincare
