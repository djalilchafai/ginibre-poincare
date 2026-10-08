module
public import GinibrePoincare.Analysis.CorrespondenceCurvatureDeficit
public import GinibrePoincare.Analysis.GinibrePointwiseCurvature
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
@[expose] public section
open Set Filter
open scoped ContDiff BigOperators ComplexConjugate Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def correspondenceImaginaryCoordinate {n : ℕ} (j : Fin n) : Configuration n →L[ℝ] ℝ :=
  Complex.imCLM.comp (ContinuousLinearMap.proj j)

theorem correspondenceImaginaryCoordinate_gradient {n : ℕ} (j : Fin n) (z : Configuration n) :
    ginibreBochnerGradient (correspondenceImaginaryCoordinate j) z = imaginaryCoordinateDirection j := by
  ext i
  rw [correspondenceBochnerGradient_coordinate]
  unfold bochnerDirectionalDerivative
  rw [(correspondenceImaginaryCoordinate j).fderiv]
  by_cases hij : i=j
  · subst i
    simp [correspondenceImaginaryCoordinate,realCoordinateDirection,imaginaryCoordinateDirection,coordinateDirection]
  · simp [hij,Ne.symm hij,correspondenceImaginaryCoordinate,realCoordinateDirection,imaginaryCoordinateDirection,
    coordinateDirection]

theorem correspondenceImaginaryCoordinate_hessian {n : ℕ} (j : Fin n) (z : Configuration n) :
    fderiv ℝ (fderiv ℝ (correspondenceImaginaryCoordinate j)) z = 0 := by
  have he : fderiv ℝ (correspondenceImaginaryCoordinate j) =
      fun _ => correspondenceImaginaryCoordinate j := by
    funext x
    exact (correspondenceImaginaryCoordinate j).fderiv
  rw [he]
  exact congrFun (fderiv_const (𝕜 := ℝ) (E := Configuration n) (correspondenceImaginaryCoordinate j)) z

theorem correspondenceImaginaryCoordinate_HessianSquare {n : ℕ} (j : Fin n) (z : Configuration n) :
    ginibreBochnerHessianSquare (correspondenceImaginaryCoordinate j) z = 0 := by
  simp [ginibreBochnerHessianSquare,correspondenceImaginaryCoordinate_hessian]

#print axioms correspondenceImaginaryCoordinate_gradient
#print axioms correspondenceImaginaryCoordinate_hessian
end
end GinibrePoincare
