module

public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityCoordinateEquation
public import GinibrePoincare.Analysis.GinibreWeakGradient

@[expose] public section
namespace GinibrePoincare
noncomputable section

theorem ginibreLocalRegularity_coordinate_basis (n : ℕ) (k : Fin n × Fin 2) :
    (configurationEuclideanEquiv n).symm (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ k) =
      ginibreCoordinateDirection k := by
  classical
  rcases k with ⟨i, j⟩
  fin_cases j <;> ext l <;> by_cases hl : l = i <;>
    simp [configurationEuclideanEquiv_symm_apply, EuclideanSpace.basisFun_apply,
      EuclideanSpace.single_apply, ginibreCoordinateDirection, realCoordinateDirection,
      imaginaryCoordinateDirection, coordinateDirection, Prod.mk.injEq, hl] <;> rfl

#print axioms ginibreLocalRegularity_coordinate_basis
end
end GinibrePoincare
