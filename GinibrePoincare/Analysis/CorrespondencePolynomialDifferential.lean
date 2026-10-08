module
public import GinibrePoincare.Analysis.CorrespondencePolynomialCoulomb
@[expose] public section
open MeasureTheory
open scoped BigOperators ComplexConjugate ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

def correspondencePolynomialCoordinate {n : ℕ} (k : Fin n × Fin 2) :
    Configuration n →L[ℝ] ℂ :=
  if k.2=0 then ContinuousLinearMap.proj k.1 else
    Complex.conjCLE.toContinuousLinearMap.comp (ContinuousLinearMap.proj k.1)

def correspondencePolynomialDerivative {n : ℕ} (P : GinibreMixedPolynomial n)
    (v : Configuration n) : GinibreMixedPolynomial n :=
  ∑ k : Fin n × Fin 2, MvPolynomial.C (correspondencePolynomialCoordinate k v) * MvPolynomial.pderiv k P

/-- Every real-direction derivative of an arbitrary mixed polynomial remains
an explicit mixed polynomial. -/
theorem correspondencePolynomial_derivative_eval {n : ℕ} (P : GinibreMixedPolynomial n)
    (z v : Configuration n) :
    fderiv ℝ (ginibreMixedPolynomialEval P) z v =
      ginibreMixedPolynomialEval (correspondencePolynomialDerivative P v) z := by
  let φ := fun k : Fin n × Fin 2 => (correspondencePolynomialCoordinate k : Configuration n → ℂ)
  have hcoord (k : Fin n × Fin 2) (y : Configuration n) : correspondencePolynomialCoordinate k y =
      if k.2=0 then y k.1 else conj (y k.1) := by
    unfold correspondencePolynomialCoordinate
    split_ifs <;> rfl
  have he : observablePolynomial φ P = ginibreMixedPolynomialEval P := by
    funext y
    simp only [observablePolynomial, ginibreMixedPolynomialEval, φ, hcoord]
  rw [← he, fderiv_observablePolynomial φ (fun k => (correspondencePolynomialCoordinate k).differentiable) P z v]
  simp only [φ, ContinuousLinearMap.fderiv]
  unfold ginibreMixedPolynomialEval correspondencePolynomialDerivative
  simp only [map_sum, map_mul, MvPolynomial.eval_C]
  apply Finset.sum_congr rfl
  intro k hk
  rw [mul_comm]
  simp only [observablePolynomial, hcoord]

/-- The real projection of a mixed polynomial has polynomial real-direction
first and second derivatives. -/
theorem correspondencePolynomial_projected_derivative {n : ℕ}
    (P : GinibreMixedPolynomial n) (T : ℂ →L[ℝ] ℝ) (z v : Configuration n) :
    fderiv ℝ (fun y => T (ginibreMixedPolynomialEval P y)) z v =
      T (ginibreMixedPolynomialEval (correspondencePolynomialDerivative P v) z) := by
  have h := T.hasFDerivAt.comp z ((correspondencePolynomial_contDiff n P).differentiable (by simp) z).hasFDerivAt
  change fderiv ℝ (T ∘ ginibreMixedPolynomialEval P) z v = _
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  rw [correspondencePolynomial_derivative_eval]

/-- Every projected polynomial and every constant-direction derivative are
in the concrete Ginibre L² space, including n=1. -/
theorem correspondencePolynomial_projected_memLp {n : ℕ} (hn : 0 < n)
    (P : GinibreMixedPolynomial n) (T : ℂ →L[ℝ] ℝ) :
    MemLp (fun z => T (ginibreMixedPolynomialEval P z)) 2 (ginibreMeasure n) :=
  T.comp_memLp' (correspondencePolynomial_ginibre_memLp hn P)

#print axioms correspondencePolynomial_derivative_eval
#print axioms correspondencePolynomial_projected_derivative
#print axioms correspondencePolynomial_projected_memLp
end
end GinibrePoincare
