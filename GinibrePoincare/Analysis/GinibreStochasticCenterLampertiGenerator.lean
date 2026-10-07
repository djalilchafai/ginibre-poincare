module

public import GinibrePoincare.Analysis.GinibreStochasticCenterLogGenerator
public import GinibrePoincare.Analysis.FiniteDimensionalItoScalarChain

@[expose] public section

/-! Exact actual square-root center generator, away from a zero center. -/
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1600000

def ginibreSquareRootCenter (n : ℕ) (z : Configuration n) : ℝ :=
  Real.sqrt (ginibreCenterSquared n z)

def ginibreLampertiCenterDrift (n : ℕ) (α r : ℝ) : ℝ :=
  (α/(n : ℝ))*(1)/(Real.sqrt r)-
    (2*α/(n : ℝ))*Real.sqrt r

theorem ginibreLampertiCenterDrift_measurable (n : ℕ) (α : ℝ) :
    Measurable (ginibreLampertiCenterDrift n α) := by
  unfold ginibreLampertiCenterDrift
  fun_prop

theorem ginibreLampertiCenterDrift_continuousOn (n : ℕ) (α : ℝ) :
    ContinuousOn (ginibreLampertiCenterDrift n α) (Set.Ioi 0) := by
  intro r hr
  exact (continuous_const.continuousAt.div (Real.continuous_sqrt.continuousAt)
    (Real.sqrt_pos.mpr hr).ne').sub (continuous_const.mul Real.continuous_sqrt).continuousAt |>.continuousWithinAt

theorem ginibreRealPaperSpeedGenerator_squareRootCenter {n : ℕ} (hn : 2 ≤ n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z)
    (hcenter : 0 < ginibreCenterSquared n z) :
    ginibreRealPaperSpeedGenerator n α (ginibreSquareRootCenter n) z =
      ginibreLampertiCenterDrift n α (ginibreCenterSquared n z) := by
  have hρ := hcenter
  have hs : Real.sqrt (ginibreCenterSquared n z) ≠ 0 := (Real.sqrt_pos.mpr hρ).ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hf : ContDiffAt ℝ 2 (ginibreCenterSquared n : Configuration n → ℝ) z :=
    ((contDiff_ginibreCenterSquared n).of_le
      (by exact WithTop.coe_le_coe.mpr (show (2 : ENat) ≤ ⊤ from le_top))).contDiffAt
  have hφ : ContDiffAt ℝ 2 Real.sqrt (ginibreCenterSquared n z) := Real.contDiffAt_sqrt hρ.ne'
  change ginibreRealPaperSpeedGenerator n α (fun w => Real.sqrt (ginibreCenterSquared n w)) z = _
  rw [ginibreRealPaperSpeedGenerator_scalar_comp α (ginibreCenterSquared n) Real.sqrt z hf hφ,
    (Real.hasDerivAt_sqrt hρ.ne').deriv,ginibre_deriv_deriv_sqrt hρ,
    ginibreRealPaperSpeedGenerator_centerSquared hn α z hz]
  have hg : realGradientNormSq (ginibreCenterSquared n) z=4*(n : ℝ)*ginibreCenterSquared n z :=
    ginibre_centerSquared_gradient_normSq n z
  rw [hg]
  unfold ginibreLampertiCenterDrift
  have hsq := Real.sq_sqrt hρ.le
  generalize he : Real.sqrt (ginibreCenterSquared n z)=r at hs hsq ⊢
  rw [← hsq]
  field_simp
  <;> ring
#print axioms ginibreRealPaperSpeedGenerator_squareRootCenter
end
end GinibrePoincare
