module

public import GinibrePoincare.Concrete.MainProofReduction
public import GinibrePoincare.Analysis.GroundStateDbar
public import GinibrePoincare.Analysis.GaussianEntireDistance
public import GinibrePoincare.Analysis.GinibreEntireProjectionEndpoints

@[expose] public section

/-! # The original analytic proof of Theorem 1.1
All five analytic inputs are unconditional compiled theorems about the concrete
measures and actual entire representative distance infima.
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
