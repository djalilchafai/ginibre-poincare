module

public import GinibrePoincare.Analysis.GeneralPotentialWeightedPolynomialPhase
public import GinibrePoincare.Analysis.GeneralPotentialPositivePhaseClosure

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem potentialInverseAlternatedVector_positive_or_bottom_or_zero {n : ℕ} (hn : 0 < n)
    {V : Potential} (hV : ContDiff ℝ 2 V) (hrot : IsRotationalPotential V)
    (hfin : potentialPartition n V < ⊤) (F : PlanarPiLebesgueL2 n)
    (hF : F ∈ planarPiAlternatedWeightedMonomialVectors n n V) :
    (potentialPiVandermondeL2Equiv n hn hV.continuous hfin).symm F ∈
        potentialPositivePhaseVectors n hV.continuous hrot ∨
      (∃ P : ConfigurationPolynomial n, P.IsHomogeneous (vandermondeDegree n) ∧
        IsAlternatingConfigurationPolynomial P ∧
        (F : Configuration n → ℂ) =ᵐ[volume]
          fun z => MvPolynomial.eval z P * piPotentialHalfWeight n n V z) ∨ F = 0 := by
  obtain ⟨D, P, hp, ha, he⟩ := planarPiAlternatedWeightedMonomialVector_homogeneous_alternating n V F hF
  by_cases hz : P = 0
  · right; right
    apply weightedPolynomialL2_eq_zero F
    simpa only [hz] using he
  have hle := vandermondeDegree_le_of_homogeneous_alternating hp ha hz
  by_cases hbottom : D = vandermondeDegree n
  · right; left
    exact ⟨P, hbottom ▸ hp, ha, he⟩
  left
  refine ⟨D - vandermondeDegree n, by omega, ?_⟩
  intro a ha
  exact potentialInverseGauge_phase_degree hn hV.continuous hrot hfin hle F
    (fun a ha => volumeGlobalPhaseL2_weighted_homogeneous hrot P hp F he a ha) a ha

end
end GinibrePoincare
