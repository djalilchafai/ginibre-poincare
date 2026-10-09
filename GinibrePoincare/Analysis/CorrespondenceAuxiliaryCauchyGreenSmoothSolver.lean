module
public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryCauchyGreenFundamental
public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryCauchyGreenPotential

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The literal Cauchy–Green convolution solves ∂bar u=a for every actual
smooth compact planar source, with a genuine smooth global solution. -/
theorem cauchyGreenPotential_solves_dbar (a : ℂ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) (z : ℂ) :
    planarDbar (cauchyGreenPotential a) z = a z := by
  let θ : ℂ → ℂ := fun y => a (z-y)
  have hθ : ContDiff ℝ 1 θ := (ha.of_le (by simp)).comp
    (contDiff_const.sub contDiff_id)
  have hcθ : HasCompactSupport θ := hc.comp_homeomorph (Homeomorph.subLeft z)
  have h := cauchyGreenKernel_fundamental_identity θ hθ hcθ
  have hder (y : ℂ) : planarDbar θ y = -planarDbar a (z-y) :=
    planarDbar_sub_left a (ha.differentiable (by simp)) z y
  simp_rw [hder, mul_neg, integral_neg] at h
  rw [cauchyGreenPotential_dbar_integral a ha hc z]
  have hh := neg_injective h
  simpa [θ] using hh

theorem cauchyGreenSmooth_compact_solvability (a : ℂ → ℂ)
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) :
    ∃ u : ℂ → ℂ, ContDiff ℝ ∞ u ∧ ∀ z, planarDbar u z = a z :=
  ⟨cauchyGreenPotential a, cauchyGreenPotential_contDiff a ha hc,
    cauchyGreenPotential_solves_dbar a ha hc⟩

#print axioms cauchyGreenPotential_solves_dbar
#print axioms cauchyGreenSmooth_compact_solvability
end
end GinibrePoincare
