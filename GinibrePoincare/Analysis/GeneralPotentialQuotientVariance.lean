module

public import GinibrePoincare.Analysis.GeneralPotentialQuotientProjection
public import GinibrePoincare.Analysis.GeneralPotentialProjectionRealVariance
public import GinibrePoincare.Analysis.GeneralPotentialPositivePhaseClosure

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Hilbert geometry for an actual centered observable whose projected vector
lies in the genuine closed positive-character space. -/
theorem potentialVariance_le_two_quotient_residual_of_positive {d : ℕ}
    (hn : 0 < d+1) {V : Potential} (hV : ContDiff ℝ 2 V) (hrot : IsRotationalPotential V)
    (hfin : potentialPartition (d+1) V < ⊤)
    (f : Configuration (d+1) → ℝ) (hf : MemLp f 2 (potentialMeasure (d+1) V))
    (hp : potentialHolomorphicQuotientProjection hn hV hfin
      (potentialCenteredL2 (d+1) hn hV.continuous hfin f hf) ∈
        potentialPositivePhaseClosedSpan (d+1) hV.continuous hrot) :
    potentialVariance (d+1) V f ≤ 2 *
      ‖potentialCenteredL2 (d+1) hn hV.continuous hfin f hf -
        potentialHolomorphicQuotientProjection hn hV hfin
          (potentialCenteredL2 (d+1) hn hV.continuous hfin f hf)‖ ^ 2 := by
  rw [← potentialCenteredL2_norm_sq (d+1) hn hV.continuous hfin f hf]
  apply real_Lp_projection_norm_sq_le_two_residual
    (potentialMeasure (d+1) V) (potentialHolomorphicQuotientProjection hn hV hfin)
    (potentialHolomorphicQuotientProjection_adjoint hn hV hfin)
    (potentialHolomorphicQuotientProjection_idempotent hn hV hfin)
    _ (potentialCenteredL2_star (d+1) hn hV.continuous hfin f hf)
  exact potentialPositivePhaseClosedSpan_inner_star_zero hV.continuous hrot _ _ hp hp

end
end GinibrePoincare
