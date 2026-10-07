module

public import GinibrePoincare.Analysis.GinibreStochasticCenterLampertiGenerator
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition

@[expose] public section

/-! Globally smooth center square-root tests, exactly equal to the original
square root above an explicit positive threshold. -/
open Set Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000

def ginibreCenterSquareRootRegularized (n : ℕ) (δ : ℝ) (z : Configuration n) : ℝ :=
  Real.sqrt (ginibreCenterSquared n z +
    δ * Real.smoothTransition (2 - 2 * ginibreCenterSquared n z / δ))

theorem contDiff_ginibreCenterSquareRootRegularized (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ ∞ (ginibreCenterSquareRootRegularized n δ) := by
  apply ContDiff.sqrt
  · exact (contDiff_ginibreCenterSquared n).add
      (contDiff_const.mul (Real.smoothTransition.contDiff.comp
        (contDiff_const.sub ((contDiff_const.mul (contDiff_ginibreCenterSquared n)).div_const δ))))
  · intro z
    have hr : 0 ≤ ginibreCenterSquared n z := Complex.normSq_nonneg _
    have hs := Real.smoothTransition.nonneg (2 - 2 * ginibreCenterSquared n z / δ)
    have hp : 0 < ginibreCenterSquared n z +
        δ * Real.smoothTransition (2 - 2 * ginibreCenterSquared n z / δ) := by
      by_cases hz : ginibreCenterSquared n z = 0
      · simp only [hz,mul_zero,zero_div,sub_zero,zero_add]
        rw [Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 2)]
        simpa using hδ
      · exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne hr (Ne.symm hz)) (mul_nonneg hδ.le hs)
    exact hp.ne'

theorem ginibreCenterSquareRootRegularized_eq {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (z : Configuration n) (hz : δ ≤ ginibreCenterSquared n z) :
    ginibreCenterSquareRootRegularized n δ z = ginibreSquareRootCenter n z := by
  have hh : 2 - 2 * ginibreCenterSquared n z / δ ≤ 0 := by
    have h := (le_div_iff₀ hδ).mpr (show 2 * δ ≤ 2 * ginibreCenterSquared n z by linarith)
    linarith
  simp [ginibreCenterSquareRootRegularized,ginibreSquareRootCenter,
    Real.smoothTransition.zero_of_nonpos hh]

theorem ginibreCenterSquareRootRegularized_eventuallyEq {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (z : Configuration n) (hz : δ < ginibreCenterSquared n z) :
    ginibreCenterSquareRootRegularized n δ =ᶠ[𝓝 z] ginibreSquareRootCenter n := by
  filter_upwards [(contDiff_ginibreCenterSquared n).continuous.continuousAt.eventually
    (eventually_gt_nhds hz)] with w hw
  exact ginibreCenterSquareRootRegularized_eq hδ w hw.le

theorem ginibrePregenerator_congr_of_eventuallyEq {n : ℕ}
    (f g : Configuration n → ℝ) (z : Configuration n)
    (h : f =ᶠ[𝓝 z] g) : ginibrePregenerator n f z = ginibrePregenerator n g z := by
  have hd := h.fderiv_eq (𝕜 := ℝ)
  have hdd (v : Configuration n) : secondDirectionalDerivative f v z =
      secondDirectionalDerivative g v z := by
    unfold secondDirectionalDerivative
    have he : (fun x => fderiv ℝ f x v) =ᶠ[𝓝 z] (fun x => fderiv ℝ g x v) := by
      filter_upwards [h.fderiv (𝕜 := ℝ)] with x hx
      rw [hx]
    rw [he.fderiv_eq]
  simp only [ginibrePregenerator,configurationLaplacian,hd,hdd]

theorem ginibreCenterSquareRootRegularized_generator {n : ℕ} (hn : 2 ≤ n)
    (α : ℝ) {δ : ℝ} (hδ : 0 < δ) (z : Configuration n)
    (hz : CollisionFree z) (hr : δ < ginibreCenterSquared n z) :
    ginibreRealPaperSpeedGenerator n α (ginibreCenterSquareRootRegularized n δ) z =
      ginibreLampertiCenterDrift n α (ginibreCenterSquared n z) := by
  unfold ginibreRealPaperSpeedGenerator
  rw [ginibrePregenerator_congr_of_eventuallyEq _ _ z
    (ginibreCenterSquareRootRegularized_eventuallyEq hδ z hr)]
  exact ginibreRealPaperSpeedGenerator_squareRootCenter hn α z hz (hδ.trans hr)

#print axioms ginibrePregenerator_congr_of_eventuallyEq
#print axioms ginibreCenterSquareRootRegularized_generator
#print axioms contDiff_ginibreCenterSquareRootRegularized
#print axioms ginibreCenterSquareRootRegularized_eventuallyEq
end
end GinibrePoincare
