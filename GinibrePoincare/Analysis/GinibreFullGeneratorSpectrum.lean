module

public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

@[expose] public section

namespace GinibrePoincare
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A positive Hilbert-space contraction has real spectrum in the unit interval. -/
theorem ginibreFull_positive_contraction_spectrum (R : H →L[ℂ] H)
    (hp : R.IsPositive) (hnorm : ‖R‖ ≤ 1) : spectrum ℝ R ⊆ Set.Icc 0 1 := by
  rcases subsingleton_or_nontrivial H with hH | hH
  · let := hH
    rw [spectrum.of_subsingleton]
    exact Set.empty_subset _
  let := hH
  intro r hr
  have hpos : 0 ≤ R := ContinuousLinearMap.nonneg_iff_isPositive.mpr hp
  exact ⟨spectrum_nonneg_of_nonneg hpos hr,
    (Real.le_norm_self r).trans ((spectrum.norm_le_norm_of_mem hr).trans hnorm)⟩

end
end GinibrePoincare
