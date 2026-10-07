module

public import GinibrePoincare.Analysis.MatrixSpectralSobolevDensityTransport

@[expose] public section

/-! # Actual independent entry law in the spectral Sobolev coordinates -/
open MeasureTheory Matrix
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem matrixComplexEntryEquiv_productGaussian_preserving {n m : ℕ}
    (e : Fin m ≃ Fin n × Fin n) :
    MeasurePreserving (matrixComplexEntryEquiv e)
      (Measure.pi (fun _ : Fin m => (complexCoordinateGaussianProbability n : Measure ℂ)))
      (matrixGaussianMeasure n) := by
  have h₁ := measurePreserving_piCongrLeft
    (fun _ : Fin n × Fin n => (complexCoordinateGaussianProbability n : Measure ℂ)) e
  have h₂ := (matrixGaussianMeasure_uncurry_preserving n).symm (matrixUncurryMeasurableEquiv n)
  convert h₂.comp h₁ using 1
  all_goals try rfl
  funext z i j
  simp [matrixComplexEntryEquiv, matrixUncurryMeasurableEquiv,
    MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

theorem matrixEntryGaussianMeasure_eq_product {n m : ℕ} (hn : 0 < n)
    (e : Fin m ≃ Fin n × Fin n) : matrixEntryGaussianMeasure e =
    Measure.pi (fun _ : Fin m => (complexCoordinateGaussianProbability n : Measure ℂ)) := by
  let η := (matrixComplexEntryEquiv e).toHomeomorph.toMeasurableEquiv
  have h₁ := (matrixComplexEntryEquiv_gaussian_preserving hn e).symm η
  have h₂ := h₁.comp (matrixComplexEntryEquiv_productGaussian_preserving e)
  have he := h₂.map_eq
  have hid : (η.symm : MatrixRealSpace n → Configuration m) ∘ matrixComplexEntryEquiv e = id := by
    funext z
    exact (matrixComplexEntryEquiv e).symm_apply_apply z
  rw [hid, Measure.map_id] at he
  exact he.symm

end
end GinibrePoincare
