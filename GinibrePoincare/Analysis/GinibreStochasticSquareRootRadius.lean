module

public import GinibrePoincare.Analysis.GinibreStochasticCIRNoiseCoefficient
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-! The actual Lamperti test is smooth on collision-free configurations and
has the constant radial Brownian noise amplitude prescribed by the paper. -/
open Set
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1200000

def ginibreSquareRootRadius {n : ℕ} (z : Configuration n) : ℝ := Real.sqrt (pairwiseRadius z)

theorem ginibre_contDiffOn_squareRootRadius {n : ℕ} (hn : 2 ≤ n) :
    ContDiffOn ℝ ∞ (ginibreSquareRootRadius : Configuration n → ℝ) {z | CollisionFree z} := by
  intro z hz
  exact ((ginibre_contDiff_pairwiseRadius n).contDiffAt.sqrt
    (ne_of_gt (pairwiseRadius_pos_of_collisionFree hn z hz))).contDiffWithinAt

theorem ginibre_fderiv_squareRootRadius {n : ℕ} (hn : 2 ≤ n)
    (z : Configuration n) (hz : CollisionFree z) (v : Configuration n) :
    fderiv ℝ ginibreSquareRootRadius z v =
      (1/(2*Real.sqrt (pairwiseRadius z)))*fderiv ℝ pairwiseRadius z v := by
  have hd : DifferentiableAt ℝ (pairwiseRadius : Configuration n → ℝ) z :=
    (ginibre_contDiff_pairwiseRadius n).differentiable (by simp) z
  change fderiv ℝ (fun w : Configuration n => Real.sqrt (pairwiseRadius w)) z v = _
  rw [fderiv_sqrt hd (ne_of_gt (pairwiseRadius_pos_of_collisionFree hn z hz))]
  rfl

theorem ginibreCIR_noise_amplitude_factor {n : ℕ} (α : ℝ) (z : Configuration n)
    (hρ : 0 ≤ pairwiseRadius z) :
    Real.sqrt ((8*α/(n : ℝ))*pairwiseRadius z) =
      (2*Real.sqrt (pairwiseRadius z))*Real.sqrt (2*α/(n : ℝ)) := by
  have he : (8*α/(n : ℝ))*pairwiseRadius z=(4*pairwiseRadius z)*(2*α/(n : ℝ)) := by ring
  have h4 : Real.sqrt (4*pairwiseRadius z)=2*Real.sqrt (pairwiseRadius z) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  rw [he, Real.sqrt_mul (mul_nonneg (by norm_num) hρ), h4]

theorem ginibre_squareRootRadius_noise_coordinate {n : ℕ} (hn : 2 ≤ n)
    (α : ℝ) (hα : 0 ≤ α) (z : Configuration n) (hz : CollisionFree z)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (i : Fin n × Fin 2) :
    Real.sqrt (2*α/(n : ℝ)^2)*fderiv ℝ ginibreSquareRootRadius z (ginibreCoordinateDirection i) =
      Real.sqrt (2*α/(n : ℝ))*ginibreRecenteredRadialDirection n e z i := by
  have hρ := pairwiseRadius_pos_of_collisionFree hn z hz
  have hs : Real.sqrt (pairwiseRadius z) ≠ 0 := (Real.sqrt_pos.mpr hρ).ne'
  rw [ginibre_fderiv_squareRootRadius hn z hz]
  calc
    _ = (1/(2*Real.sqrt (pairwiseRadius z)))*
        (Real.sqrt (2*α/(n : ℝ)^2)*fderiv ℝ pairwiseRadius z (ginibreCoordinateDirection i)) := by ring
    _ = _ := by
      rw [ginibreCIR_noise_coordinate hn α hα z hz e i, ginibreCIR_noise_amplitude_factor α z hρ.le]
      field_simp
      <;> ring
end
end GinibrePoincare
