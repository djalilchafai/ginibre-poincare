module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianGlobal
public import GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsLSI
@[expose] public section
open MeasureTheory ProbabilityTheory Set
namespace GinibrePoincare
noncomputable section

/-- Concrete strongly convex normalized Gibbs log-Sobolev inequality on real
Euclidean coordinates. Brownian noise, global Langevin flow, Gibbs invariance
and the entropy limit are all constructed internally. -/
theorem bakryEmeryConfigurationGibbs_square_lsi
    (n : ℕ) (hn : 0 < n) (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W)
    (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n×Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2))
    (f : EuclideanSpace ℝ (Fin n×Fin 2) → ℝ) (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    squareEntropy (bakryEmeryNormalizedGibbs volume (W ∘ (configurationEuclideanEquiv n).symm)) f ≤
      (2/κ)*∫ x, ‖gradient f x‖^2 ∂bakryEmeryNormalizedGibbs volume
        (W ∘ (configurationEuclideanEquiv n).symm) := by
  exact bakryEmeryConfigurationGibbs_square_lsi_of_Brownian n hn W hW κ hκ hc
    (bakryBrownianCoordinateProcess (Fin n×Fin 2)) (bakryBrownianCoordinateMeasure (Fin n×Fin 2))
    (bakryBrownianCoordinate_isBrownian (Fin n×Fin 2))
    (bakryBrownianCoordinate_independent (Fin n×Fin 2)) f hf hs

#print axioms bakryEmeryConfigurationGibbs_square_lsi
end
end GinibrePoincare
