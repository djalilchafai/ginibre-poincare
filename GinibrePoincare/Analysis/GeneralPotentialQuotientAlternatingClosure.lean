module

public import GinibrePoincare.Analysis.GeneralPotentialQuotientProjection
public import GinibrePoincare.Analysis.GeneralPotentialProjectionGeometry
public import GinibrePoincare.Analysis.NonQuadraticAlternatingMonomialClosure

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem potentialHolomorphicQuotient_centered_gauge_mem_alternated_closure {d : ℕ}
    (hn : 0 < d+1) {V : Potential} (hV : ContDiff ℝ 2 V) (hrot : IsRotationalPotential V)
    (hfin : potentialPartition (d+1) V < ⊤)
    (f : Configuration (d+1) → ℝ) (hf : MemLp f 2 (potentialMeasure (d+1) V))
    (hs : IsSymmetric f) :
    potentialPiVandermondeL2Equiv (d+1) hn hV.continuous hfin
      (potentialHolomorphicQuotientProjection hn hV hfin
        (potentialCenteredL2 (d+1) hn hV.continuous hfin f hf)) ∈
      (Submodule.span ℂ (planarPiAlternatedWeightedMonomialVectors (d+1) (d+1) V)).topologicalClosure := by
  rw [potentialHolomorphicQuotientProjection_gauge]
  apply planarPiBergman_alternating_mem_alternated_monomial_closure
    (d+1) V hV (fun a ha z => hrot a z ha)
  intro e
  exact potentialVandermondeCentered_alternating (d+1) hn hV.continuous hfin f hf hs e

end
end GinibrePoincare
