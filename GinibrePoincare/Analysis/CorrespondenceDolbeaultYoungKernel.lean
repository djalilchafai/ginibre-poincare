module
public import GinibrePoincare.Analysis.CorrespondenceDolbeaultYoungPairing
public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryCauchyGreenKernel

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section

def dolbeaultTruncatedCauchyGreen (R : ℝ) : ℂ → ℂ :=
  (Metric.closedBall 0 R).indicator cauchyGreenKernel

theorem dolbeaultTruncatedCauchyGreen_integrable (R : ℝ) :
    Integrable (dolbeaultTruncatedCauchyGreen R) volume := by
  exact (integrable_indicator_iff measurableSet_closedBall).mpr
    (cauchyGreenKernel_locallyIntegrable.integrableOn_isCompact
      (isCompact_closedBall (0 : ℂ) R))

/-- The locally singular Cauchy–Green kernel gives a genuine bounded coordinate
homotopy on ordinary L² after truncation; no L² assumption on the kernel is used. -/
def dolbeaultCauchyGreenL2 {n : ℕ} (j : Fin n) (R : ℝ) :
    dolbeaultOrdinaryL2 n →L[ℂ] dolbeaultOrdinaryL2 n :=
  dolbeaultCoordinateConvolutionCLM j (dolbeaultTruncatedCauchyGreen R)
    (dolbeaultTruncatedCauchyGreen_integrable R)

theorem dolbeaultCauchyGreenL2_norm {n : ℕ} (j : Fin n) (R : ℝ)
    (u : dolbeaultOrdinaryL2 n) :
    ‖dolbeaultCauchyGreenL2 j R u‖ ≤
      (∫ y : ℂ, ‖dolbeaultTruncatedCauchyGreen R y‖)*‖u‖ :=
  dolbeaultCoordinateConvolution_norm j (dolbeaultTruncatedCauchyGreen R) u

#print axioms dolbeaultTruncatedCauchyGreen_integrable
#print axioms dolbeaultCauchyGreenL2_norm
end
end GinibrePoincare
