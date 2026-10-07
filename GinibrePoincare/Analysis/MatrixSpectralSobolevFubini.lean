module

public import GinibrePoincare.Analysis.MatrixSpectralSobolevFTC
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! # Distributional derivative transport from actual spectral line slices -/
open MeasureTheory Filter
namespace GinibrePoincare
noncomputable section

/-- Actual continuous line slices with integrable derivatives off finitely many
points imply the ordinary distributional test identity under product measure. -/
theorem product_weak_derivative_identity_of_finite_crossings
    {Y : Type*} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν]
    (f g ψ ψ' : ℝ × Y → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hψ : ∀ y, ContDiff ℝ 1 (fun t => ψ (t, y)))
    (hψ' : ∀ t y, deriv (fun s => ψ (s, y)) t = ψ' (t, y))
    (hsupp : ∀ y, tsupport (fun t => ψ (t, y)) ⊆ Set.Ioo a b)
    (hslice : ∀ᵐ y ∂ν, Continuous (fun t => f (t, y)) ∧
      LocallyIntegrable (fun t => g (t, y)) volume ∧
      ∃ S : Finset ℝ, ∀ t, t ∉ S →
        HasDerivAt (fun s => f (s, y)) (g (t, y)) t)
    (hgi : Integrable (fun z => g z * ψ z) ((volume : Measure ℝ).prod ν))
    (hfi : Integrable (fun z => f z * ψ' z) ((volume : Measure ℝ).prod ν)) :
    (∫ z, g z * ψ z ∂((volume : Measure ℝ).prod ν)) =
      -(∫ z, f z * ψ' z ∂((volume : Measure ℝ).prod ν)) := by
  rw [integral_prod_symm _ hgi, integral_prod_symm _ hfi, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [hslice] with y hy
  obtain ⟨hf, hg, S, hd⟩ := hy
  have h := weak_derivative_test_identity_off_finite S (fun t => f (t, y))
    (fun t => g (t, y)) (fun t => ψ (t, y)) hf hg hd (hψ y) a b hab (hsupp y)
  simpa only [hψ'] using h

end
end GinibrePoincare
