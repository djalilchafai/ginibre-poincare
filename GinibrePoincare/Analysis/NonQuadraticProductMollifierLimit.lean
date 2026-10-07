module

public import GinibrePoincare.Analysis.NonQuadraticPlanarMollifierOperator

@[expose] public section

/-! # Genuine simultaneous separated mollifier convergence -/
open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem contractions_strong_limit_apply
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (T : ℕ → H →L[ℂ] H) (hb : ∀ m, ‖T m‖ ≤ 1)
    (hu : ∀ u, Tendsto (fun m => T m u) atTop (𝓝 u))
    (v : ℕ → H) (u : H) (hv : Tendsto v atTop (𝓝 u)) :
    Tendsto (fun m => T m (v m)) atTop (𝓝 u) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hv' := tendsto_iff_norm_sub_tendsto_zero.mp hv
  have ht' := tendsto_iff_norm_sub_tendsto_zero.mp (hu u)
  have hl : Tendsto (fun m => ‖v m - u‖ + ‖T m u - u‖) atTop (𝓝 0) := by
    simpa only [zero_add] using hv'.add ht'
  apply squeeze_zero (fun m => norm_nonneg _) (fun m => ?_) hl
  have h : ‖T m (v m) - u‖ ≤ ‖T m (v m) - T m u‖ + ‖T m u - u‖ := by
    simpa only [dist_eq_norm] using dist_triangle (T m (v m)) (T m u) u
  have he : ‖T m (v m) - T m u‖ ≤ ‖v m - u‖ := by
    rw [← map_sub]
    have hb' := mul_le_mul_of_nonneg_right (hb m) (norm_nonneg (v m - u))
    exact ((T m).le_opNorm _).trans (by simpa only [one_mul] using hb')
  exact h.trans (add_le_add he (le_refl _))

/-- Simultaneous left and right actual planar convolution operators
converge on every vector of the whole product Lebesgue L² space. -/
theorem planarProductMollifier_tendsto
    (φ ψ : ℕ → ContDiffBump (0 : ℂ))
    (hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0))
    (hψ : Tendsto (fun m => (ψ m).rOut) atTop (𝓝 0))
    (u : Lp ℂ 2 ((volume : Measure ℂ).prod volume)) :
    Tendsto (fun m => l2ProductLeftOperator (ν := (volume : Measure ℂ)) (planarMollifierOperator (φ m))
      (l2ProductRightOperator (μ := (volume : Measure ℂ)) (planarMollifierOperator (ψ m)) u))
      atTop (𝓝 u) := by
  apply contractions_strong_limit_apply
    (fun m => l2ProductLeftOperator (ν := (volume : Measure ℂ)) (planarMollifierOperator (φ m)))
    _ (planarProductLeftMollifier_tendsto φ hφ) _ u (planarProductRightMollifier_tendsto ψ hψ u)
  intro m
  exact (l2ProductLeftOperator_norm_le (planarMollifierOperator (φ m))).trans
    (planarMollifierOperator_norm_le (φ m))
end
end GinibrePoincare
