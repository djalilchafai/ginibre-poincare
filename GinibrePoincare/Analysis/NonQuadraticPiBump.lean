module

public import GinibrePoincare.Analysis.LebesgueL2Mollification
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 60000

def piPlanarBump (d : ℕ) (φ : ContDiffBump (0 : ℂ)) (x : Configuration d) : ℝ :=
  ∏ i, φ.normed volume (x i)

theorem piPlanarBump_continuous (d : ℕ) (φ : ContDiffBump (0 : ℂ)) : Continuous (piPlanarBump d φ) :=
  continuous_finsetProd _ (fun i _ => φ.continuous_normed.comp (continuous_apply i))

theorem piPlanarBump_compact (d : ℕ) (φ : ContDiffBump (0 : ℂ)) : HasCompactSupport (piPlanarBump d φ) := by
  have hs : IsCompact {x : Configuration d | ∀ i, x i ∈ tsupport (φ.normed (volume : Measure ℂ))} :=
    isCompact_pi_infinite (fun _ => φ.hasCompactSupport_normed)
  apply hs.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hs.isClosed
  intro x hx i
  apply subset_closure
  intro hz
  exact hx (Finset.prod_eq_zero (Finset.mem_univ i) hz)

theorem piPlanarBump_integral (d : ℕ) (φ : ContDiffBump (0 : ℂ)) :
    (∫ x : Configuration d, piPlanarBump d φ x) = 1 := by
  change (∫ x : Configuration d, (∏ i, φ.normed volume (x i))
    ∂Measure.pi (fun _ => (volume : Measure ℂ))) = 1
  rw [integral_fintype_prod_eq_prod (fun _ : Fin d => φ.normed volume)]
  simp only [φ.integral_normed, Finset.prod_const_one]

theorem piPlanarBump_nonneg (d : ℕ) (φ : ContDiffBump (0 : ℂ)) (x : Configuration d) :
    0 ≤ piPlanarBump d φ x := Finset.prod_nonneg (fun _ _ => φ.nonneg_normed _)

theorem piPlanarBump_support_ball (d : ℕ) (φ : ContDiffBump (0 : ℂ)) (x : Configuration d)
    (hx : x ∈ Function.support (piPlanarBump d φ)) : dist x 0 < φ.rOut := by
  rw [dist_zero_right]
  apply (pi_norm_lt_iff φ.rOut_pos).mpr
  intro i
  have hm : x i ∈ Function.support (φ.normed (volume : Measure ℂ)) :=
    fun h => hx (Finset.prod_eq_zero (Finset.mem_univ i) h)
  rw [φ.support_normed_eq] at hm
  simpa only [Metric.mem_ball, dist_zero_right] using hm
end
end GinibrePoincare
