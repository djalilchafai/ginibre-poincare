module

public import GinibrePoincare.Analysis.MatrixSpectralLiftEntryLp

@[expose] public section

open Matrix MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

/-- Actual positive Gaussian entry density makes weighted and ordinary volume
almost-everywhere representatives identical. -/
theorem matrixEntryGaussian_ae_iff_volume {n m : ℕ} (hn : 0 < n)
    (e : Fin m ≃ Fin n × Fin n) (p : Configuration m → Prop) :
    (∀ᵐ x ∂matrixEntryGaussianMeasure e, p x) ↔ ∀ᵐ x ∂volume, p x := by
  rw [matrixEntryGaussianMeasure_eq_real_density e,
    ae_withDensity_iff (matrixEntryGaussianDensityReal_continuous e).measurable.ennreal_ofReal]
  have hpos : ∀ x, ENNReal.ofReal (matrixEntryGaussianDensityReal e x) ≠ 0 :=
    fun x => ne_of_gt (ENNReal.ofReal_pos.mpr (matrixEntryGaussianDensityReal_pos hn e x))
  constructor
  · intro h
    filter_upwards [h] with x hx
    exact hx (hpos x)
  · intro h
    filter_upwards [h] with x hx
    exact fun _ => hx

#print axioms matrixEntryGaussian_ae_iff_volume
end
end GinibrePoincare
