module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryLiftLSILimit
public import GinibrePoincare.Analysis.AlternativeBakryEmeryLiftProbability
public import GinibrePoincare.Analysis.AlternativeBakryEmeryBoundedLSIClosure
@[expose] public section
open MeasureTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- The actual nonquadratic Euclidean lift satisfies the sharp curvature-bound
inequality on the bounded Lipschitz domain, with ordinary gradient energy. -/
theorem bakryEmeryEuclideanLift_boundedLipschitz_square_lsi
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (ρ : ℝ) (hρ : 0 < ρ)
    (V : Potential) (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (f : EuclideanSpace ℝ (Fin d × Fin 2) → ℝ)
    {K : ℝ≥0} (hf : LipschitzWith K f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    squareEntropy (bakryEmeryNormalizedGibbs volume (bakryEmeryEuclideanLiftPotential n V)) f ≤
      (2/((n:ℝ)*ρ)) * ∫ x, ‖gradient f x‖^2 ∂bakryEmeryNormalizedGibbs volume
        (bakryEmeryEuclideanLiftPotential n V) := by
  let E := EuclideanSpace ℝ (Fin d × Fin 2)
  let μ := bakryEmeryNormalizedGibbs (volume : Measure E) (bakryEmeryEuclideanLiftPotential n V)
  letI : IsProbabilityMeasure μ := bakryEmeryEuclideanLift_gibbs_probability n hn ρ hρ V hV.continuous hrot hc
  exact bakryEmery_boundedLipschitz_gradient_lsi_of_compact E volume μ
    (bakryEmeryEuclideanLift_gibbs_absolutelyContinuous n V) (2/((n:ℝ)*ρ))
    (fun g hg hgs => bakryEmeryEuclideanLift_square_lsi n d hn hd ρ hρ V hV hrot hc g hg hgs)
    f hf C hC

#print axioms bakryEmeryEuclideanLift_boundedLipschitz_square_lsi
end
end GinibrePoincare
