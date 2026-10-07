module

public import GinibrePoincare.Analysis.GinibreStochasticLocalTestIto
public import GinibrePoincare.Analysis.GinibreDynamicsGenerator

@[expose] public section

/-! Genuine real CIR coefficients and smooth radial tests for the actual Brownian SDE. -/
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000

theorem ginibre_contDiff_center_normSq (n : ℕ) :
    ContDiff ℝ ∞ (fun z : Configuration n => Complex.normSq (coordinateSum z)) := by
  have hc : ContDiff ℝ ∞ (coordinateSum : Configuration n → ℂ) := by
    simpa only [coordinateSumCLM_apply] using
      (show ContDiff ℝ ∞ (fun z => coordinateSumCLM n z) from (coordinateSumCLM n).contDiff)
  have hr : ContDiff ℝ ∞ (fun z : Configuration n => (coordinateSum z).re) := Complex.reCLM.contDiff.comp hc
  have hi : ContDiff ℝ ∞ (fun z : Configuration n => (coordinateSum z).im) := Complex.imCLM.contDiff.comp hc
  convert! (hr.mul hr).add (hi.mul hi) using 1

theorem ginibre_contDiff_pairwiseRadius (n : ℕ) :
    ContDiff ℝ ∞ (pairwiseRadius : Configuration n → ℝ) := by
  have h := ((contDiff_const : ContDiff ℝ ∞ (fun _ : Configuration n => (n : ℝ))).mul (contDiff_configurationNormSq (n := n))).sub
    (ginibre_contDiff_center_normSq n)
  convert! h using 1
  funext z
  exact pairwiseRadius_eq_normSq z

theorem ginibreRealPaperSpeedGenerator_pairwiseRadius {n : ℕ} (hn : 2 ≤ n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z) :
    ginibreRealPaperSpeedGenerator n α pairwiseRadius z =
      (4*α/(n : ℝ))*((recenteredGammaShape n : ℝ)-pairwiseRadius z) := by
  have h := congrArg Complex.re (ginibrePaperSpeedGenerator_radius n hn α z hz)
  simpa [ginibrePaperSpeedGenerator,ginibreRealPaperSpeedGenerator,complexGinibrePregenerator,
    sumRadiusPolynomial,observablePolynomial,sumRadiusCoordinate,complexRadius] using h
theorem ginibreRealPaperSpeedGenerator_pairwiseRadius_square {n : ℕ} (hn : 2 ≤ n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z) :
    ginibreRealPaperSpeedGenerator n α (fun w => pairwiseRadius w^2) z =
      2*pairwiseRadius z*((4*α/(n : ℝ))*((recenteredGammaShape n : ℝ)-pairwiseRadius z))+
        (8*α/(n : ℝ))*pairwiseRadius z := by
  have hop : sumRadiusOperator n ((MvPolynomial.X 2)^2) =
      2*MvPolynomial.X 2*(4*MvPolynomial.C (recenteredGammaShape n : ℂ)-4*MvPolynomial.X 2)+
        8*MvPolynomial.X 2 := by
    have h := sumRadiusOperator_radius_carreDuChamp n
    rw [sumRadiusOperator_radius] at h
    linear_combination h
  have h := complexGinibrePregenerator_sumRadiusPolynomial n hn ((MvPolynomial.X 2)^2) z hz
  rw [hop] at h
  have hr := congrArg Complex.re h
  have hb : ginibrePregenerator n (fun w => pairwiseRadius w^2) z =
      2*pairwiseRadius z*(4*(recenteredGammaShape n : ℝ)-4*pairwiseRadius z)+8*pairwiseRadius z := by
    simpa [complexGinibrePregenerator,sumRadiusPolynomial,observablePolynomial,sumRadiusCoordinate,
      complexRadius, ← Complex.ofReal_pow] using hr
  rw [ginibreRealPaperSpeedGenerator,hb]
  ring

end
end GinibrePoincare
