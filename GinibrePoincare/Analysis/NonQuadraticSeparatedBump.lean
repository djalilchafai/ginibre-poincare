module

public import GinibrePoincare.Analysis.NonQuadraticProductPlaneL2Mollification

@[expose] public section

/-! # Genuine normalized separated planar kernels -/
open MeasureTheory Filter
open scoped Topology ENNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

def separatedPlanarBump (φ ψ : ContDiffBump (0 : ℂ)) (x : ℂ × ℂ) : ℝ :=
  φ.normed volume x.1 * ψ.normed volume x.2

theorem separatedPlanarBump_continuous (φ ψ : ContDiffBump (0 : ℂ)) :
    Continuous (separatedPlanarBump φ ψ) :=
  (φ.continuous_normed.comp continuous_fst).mul (ψ.continuous_normed.comp continuous_snd)

theorem separatedPlanarBump_compact (φ ψ : ContDiffBump (0 : ℂ)) :
    HasCompactSupport (separatedPlanarBump φ ψ) := by
  have hS : IsCompact ((tsupport (φ.normed volume)).prod (tsupport (ψ.normed volume))) :=
    IsCompact.prod φ.hasCompactSupport_normed ψ.hasCompactSupport_normed
  apply hS.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hS.isClosed
  intro x hx
  exact ⟨subset_closure (fun h => hx (by simp [separatedPlanarBump, h])),
    subset_closure (fun h => hx (by simp [separatedPlanarBump, h]))⟩

theorem separatedPlanarBump_integral (φ ψ : ContDiffBump (0 : ℂ)) :
    ∫ x, separatedPlanarBump φ ψ x ∂((volume : Measure ℂ).prod volume) = 1 := by
  unfold separatedPlanarBump
  rw [integral_prod_mul, φ.integral_normed, ψ.integral_normed, one_mul]

theorem separatedPlanarBump_nonneg (φ ψ : ContDiffBump (0 : ℂ)) (x : ℂ × ℂ) :
    0 ≤ separatedPlanarBump φ ψ x :=
  mul_nonneg (φ.nonneg_normed _) (ψ.nonneg_normed _)

theorem separatedPlanarBump_support_ball (φ ψ : ContDiffBump (0 : ℂ))
    (x : ℂ × ℂ) (hx : x ∈ Function.support (separatedPlanarBump φ ψ)) :
    dist x 0 < max φ.rOut ψ.rOut := by
  have hφ : φ.normed volume x.1 ≠ 0 := fun h => hx (by simp [separatedPlanarBump, h])
  have hψ : ψ.normed volume x.2 ≠ 0 := fun h => hx (by simp [separatedPlanarBump, h])
  have h1 : dist x.1 0 < φ.rOut := by
    have hm : x.1 ∈ Function.support (φ.normed (volume : Measure ℂ)) := hφ
    rw [φ.support_normed_eq] at hm
    exact Metric.mem_ball.mp hm
  have h2 : dist x.2 0 < ψ.rOut := by
    have hm : x.2 ∈ Function.support (ψ.normed (volume : Measure ℂ)) := hψ
    rw [ψ.support_normed_eq] at hm
    exact Metric.mem_ball.mp hm
  simpa only [Prod.dist_eq, Prod.fst_zero, Prod.snd_zero] using
    max_lt (h1.trans_le (le_max_left _ _)) (h2.trans_le (le_max_right _ _))
end
end GinibrePoincare
