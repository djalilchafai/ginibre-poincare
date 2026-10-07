module

public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic

@[expose] public section

/-! # Extracting the scalar convex radial profile
The planar convexity assumption implies convexity and monotonicity of the
profile on the nonnegative half-line, as required by the dimension lift.
-/
namespace GinibrePoincare

/-- Restriction of a convex planar radial function to the real axis. -/
theorem convexOn_abs_of_convexOn_complex_norm {ψ : ℝ → ℝ}
    (hc : ConvexOn ℝ Set.univ (fun z : ℂ => ψ ‖z‖)) :
    ConvexOn ℝ Set.univ (fun r : ℝ => ψ |r|) := by
  have h := hc.comp_linearMap Complex.ofRealCLM.toLinearMap
  simpa [Function.comp_def, Complex.norm_real, Real.norm_eq_abs] using h

/-- The profile of a convex even function is convex on the nonnegative ray. -/
theorem convexOn_profile_of_convexOn_abs {ψ : ℝ → ℝ}
    (hc : ConvexOn ℝ Set.univ (fun r : ℝ => ψ |r|)) :
    ConvexOn ℝ (Set.Ici 0) ψ := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy a b ha hb hab
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  have ht : 0 ≤ a * x + b * y := add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
  have h := hc.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  simpa only [smul_eq_mul, abs_of_nonneg hx, abs_of_nonneg hy, abs_of_nonneg ht] using h

/-- Convexity of an even function forces its radial profile to increase. -/
theorem monotoneOn_profile_of_convexOn_abs {ψ : ℝ → ℝ}
    (hc : ConvexOn ℝ Set.univ (fun r : ℝ => ψ |r|)) :
    MonotoneOn ψ (Set.Ici 0) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  by_cases hy0 : y = 0
  · have hx0 : x = 0 := le_antisymm (hy0 ▸ hxy) hx
    simp [hx0, hy0]
  have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  let a : ℝ := (y + x) / (2 * y)
  let b : ℝ := (y - x) / (2 * y)
  have ha : 0 ≤ a := div_nonneg (add_nonneg hy hx) (by positivity)
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hxy) (by positivity)
  have hab : a + b = 1 := by dsimp [a, b]; field_simp; ring
  have heq : a * y + b * (-y) = x := by dsimp [a, b]; field_simp; ring
  have h := hc.2 (Set.mem_univ y) (Set.mem_univ (-y)) ha hb hab
  simp only [smul_eq_mul, heq, abs_neg, abs_of_nonneg hy, abs_of_nonneg hx] at h
  calc ψ x ≤ a * ψ y + b * ψ y := h
       _ = ψ y := by rw [← add_mul, hab, one_mul]

/-- Planar radial convexity supplies both scalar hypotheses of the lift. -/
theorem radial_profile_convex_monotone {ψ : ℝ → ℝ}
    (hc : ConvexOn ℝ Set.univ (fun z : ℂ => ψ ‖z‖)) :
    ConvexOn ℝ (Set.Ici 0) ψ ∧ MonotoneOn ψ (Set.Ici 0) := by
  have h := convexOn_abs_of_convexOn_complex_norm hc
  exact ⟨convexOn_profile_of_convexOn_abs h, monotoneOn_profile_of_convexOn_abs h⟩

#print axioms radial_profile_convex_monotone
end GinibrePoincare
