module

public import GinibrePoincare.Analysis.GaussianDensity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

@[expose] public section

/-! # Transporting densities through measure-preserving equivalences -/

open MeasureTheory

namespace MeasureTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}

/-- A density pulled back along a measure-preserving measurable equivalence
pushes forward to the original density. -/
theorem MeasurePreserving.map_withDensity_comp
    (e : α ≃ᵐ β) (h : MeasurePreserving e μ ν)
    {f : β → ENNReal} (hf : Measurable f) :
    Measure.map e (μ.withDensity (f ∘ e)) = ν.withDensity f := by
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply _ (e.measurable hs), withDensity_apply _ hs]
  exact h.setLIntegral_comp_preimage hs hf

/-- Specialization to the standard real-coordinate representation of `ℂ`. -/
theorem map_complexPi_withDensity
    {f : ℂ → ENNReal} (hf : Measurable f) :
    Measure.map Complex.measurableEquivPi.symm
        ((volume : Measure (Fin 2 → ℝ)).withDensity
          (f ∘ Complex.measurableEquivPi.symm)) =
      (volume : Measure ℂ).withDensity f := by
  exact MeasurePreserving.map_withDensity_comp _
    Complex.volume_preserving_equiv_pi.symm hf

end MeasureTheory
