module

public import GinibrePoincare.Concrete.MainProofReduction
public import GinibrePoincare.Analysis.GroundStateDbar
public import GinibrePoincare.Analysis.GaussianEntireDistance
public import GinibrePoincare.Analysis.GinibreEntireProjectionEndpoints

@[expose] public section

/-! # The original analytic proof of Theorem 1.1
All five analytic inputs are unconditional compiled theorems about the concrete
measures and actual entire representative distance infima.

Read `Concrete/MainProofReduction.lean` for the four scalar relations that
combine into the inequality. Here the five analytic propositions, including
admissibility, are filled by their proved concrete endpoints. Their order is:
domain admissibility, energy transport, Gaussian dbar estimate, isometric
distance transport, and real holomorphic-antiholomorphic half-distance geometry.
The ordinary weak-domain extension and equality classification are separate
endpoints; this theorem itself concerns the symmetric smooth compact core.
-/
namespace GinibrePoincare

/-- The paper's original smooth compact symmetric Poincaré proof, with no
analytic fact supplied as a theorem argument. -/
theorem fullMainAnalyticProof : SmoothGinibrePoincareStatement :=
  smoothGinibrePoincare_of_main_analytic_statements
    groundStateAdmissibility groundStateEnergyIdentity gaussianDbarEstimateStatement
    groundStateDistanceIdentityStatement ginibreHalfDistanceStatement

end GinibrePoincare
#print axioms GinibrePoincare.fullMainAnalyticProof
