module

public import GinibrePoincare.Analysis.GinibreStochasticCIRGenerator

@[expose] public section

open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000

def ginibreCenterSquared (n : ℕ) (z : Configuration n) : ℝ := Complex.normSq (coordinateSum z)

theorem contDiff_ginibreCenterSquared (n : ℕ) : ContDiff ℝ ∞ (ginibreCenterSquared n) :=
  ginibre_contDiff_center_normSq n

theorem ginibreRealPaperSpeedGenerator_centerSquared {n : ℕ} (hn : 2 ≤ n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z) :
    ginibreRealPaperSpeedGenerator n α (ginibreCenterSquared n) z =
      (4*α/(n : ℝ))*(1-ginibreCenterSquared n z) := by
  unfold ginibreCenterSquared
  have h := congrArg Complex.re (ginibrePaperSpeedGenerator_centerNormSq n hn α z hz)
  simpa [ginibrePaperSpeedGenerator, ginibreRealPaperSpeedGenerator, complexGinibrePregenerator,
    sumRadiusPolynomial, centerNormSqPolynomial, observablePolynomial, sumRadiusCoordinate,
    ginibreCenterSquared, Complex.normSq_apply] using h

end
end GinibrePoincare
