module

public import GinibrePoincare.Analysis.GeneralPotentialAlternatedPhaseClassification
public import GinibrePoincare.Analysis.GeneralPotentialNonnegativePhaseGeometry
public import GinibrePoincare.Analysis.GeneralPotentialQuotientAlternatingClosure
public import GinibrePoincare.Analysis.GeneralPotentialQuotientCentering
public import GinibrePoincare.Analysis.NonQuadraticBottomGaugeConstant

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem potentialInverseAlternatedVector_mem_nonnegative {n : ℕ} (hn : 0 < n)
    {V : Potential} (hV : ContDiff ℝ 2 V) (hrot : IsRotationalPotential V)
    (hfin : potentialPartition n V < ⊤) (F : PlanarPiLebesgueL2 n)
    (hF : F ∈ planarPiAlternatedWeightedMonomialVectors n n V) :
    (potentialPiVandermondeL2Equiv n hn hV.continuous hfin).symm F ∈
      potentialNonnegativePhaseClosedSpan n hn hV.continuous hrot hfin := by
  rcases potentialInverseAlternatedVector_positive_or_bottom_or_zero hn hV hrot hfin F hF with
    hp | hb | hz
  · apply potentialPositivePhaseClosedSpan_le_nonnegative n hn hV.continuous hrot hfin
    exact (Submodule.span ℂ (potentialPositivePhaseVectors n hV.continuous hrot)).le_topologicalClosure
      (Submodule.subset_span hp)
  · obtain ⟨P, hh, ha, he⟩ := hb
    obtain ⟨c, hc⟩ := potentialInverseGauge_bottom_polynomial_constant hn hV hrot hfin P hh ha F he
    rw [hc]
    exact potentialConstantL2_mem_nonnegativePhaseClosedSpan n hn hV.continuous hrot hfin c
  · rw [hz, map_zero]
    exact Submodule.zero_mem _

theorem potentialInverseAlternatedClosure_mem_nonnegative {n : ℕ} (hn : 0 < n)
    {V : Potential} (hV : ContDiff ℝ 2 V) (hrot : IsRotationalPotential V)
    (hfin : potentialPartition n V < ⊤) (F : PlanarPiLebesgueL2 n)
    (hF : F ∈ (Submodule.span ℂ (planarPiAlternatedWeightedMonomialVectors n n V)).topologicalClosure) :
    (potentialPiVandermondeL2Equiv n hn hV.continuous hfin).symm F ∈
      potentialNonnegativePhaseClosedSpan n hn hV.continuous hrot hfin := by
  let E := (potentialPiVandermondeL2Equiv n hn hV.continuous hfin).symm
  let K := potentialNonnegativePhaseClosedSpan n hn hV.continuous hrot hfin
  let A := K.toSubmodule.comap E.toLinearEquiv.toLinearMap
  have ha : IsClosed (A : Set (PlanarPiLebesgueL2 n)) := K.isClosed.preimage E.continuous
  have hs : Submodule.span ℂ (planarPiAlternatedWeightedMonomialVectors n n V) ≤ A := by
    apply Submodule.span_le.mpr
    intro G hG
    exact potentialInverseAlternatedVector_mem_nonnegative hn hV hrot hfin G hG
  exact (Submodule.topologicalClosure_minimal _ hs ha) hF

theorem potentialHolomorphicQuotient_centered_mem_positive {d : ℕ}
    (hn : 0 < d+1) {V : Potential} (hV : ContDiff ℝ 2 V) (hrot : IsRotationalPotential V)
    (hfin : potentialPartition (d+1) V < ⊤)
    (f : Configuration (d+1) → ℝ) (hf : MemLp f 2 (potentialMeasure (d+1) V))
    (hs : IsSymmetric f) :
    potentialHolomorphicQuotientProjection hn hV hfin
      (potentialCenteredL2 (d+1) hn hV.continuous hfin f hf) ∈
        potentialPositivePhaseClosedSpan (d+1) hV.continuous hrot := by
  apply potentialNonnegativePhase_mem_positive_of_orthogonal_constant
    (d+1) hn hV.continuous hrot hfin
  · have he := potentialInverseAlternatedClosure_mem_nonnegative hn hV hrot hfin _
      (potentialHolomorphicQuotient_centered_gauge_mem_alternated_closure hn hV hrot hfin f hf hs)
    simpa only [LinearIsometryEquiv.symm_apply_apply] using he
  · exact potentialHolomorphicQuotientProjection_centered_orthogonal_constant hn hV hrot hfin f hf 1

end
end GinibrePoincare
