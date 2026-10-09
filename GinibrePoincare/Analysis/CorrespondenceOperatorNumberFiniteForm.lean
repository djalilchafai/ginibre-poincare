module
public import GinibrePoincare.Analysis.CorrespondenceOperatorNumberDomain
@[expose] public section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section
open ComplexHermite
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
theorem correspondenceOperator_finite_hermite_inner {n : ℕ} (hn : 0<n)
    (c : HermiteMultiIndex n→₀ℂ) (u : Lp ℂ 2 (complexGaussianMeasure n)) :
    inner ℂ (finiteHermiteCombination n hn c) u=
      c.sum (fun pq a=>conj a*gaussianHermiteCoefficient hn u pq) := by
  classical
  simp [finiteHermiteCombination, Finsupp.linearCombination_apply, Finsupp.sum,
    sum_inner, inner_smul_left, gaussianHermiteCoefficient_eq_inner, hermiteL2Family, multivariateNormalizedL2]

/-- The literal raising polynomial is the Hilbert adjoint of the ordinary
weak dbar derivative against every finite Hermite polynomial. -/
theorem correspondenceOperator_finite_raising_adjoint {n : ℕ} (hn : 0<n)
    (c : HermiteMultiIndex n→₀ℂ) (u D : Lp ℂ 2 (complexGaussianMeasure n))
    (j : Fin n) (hu : IsGaussianWeakDbar n u D j) :
    inner ℂ (finiteHermiteCombination n hn (spectralRaisingCoefficients n j c)) u=
      inner ℂ (finiteHermiteCombination n hn c) D := by
  classical
  have he : finiteHermiteCombination n hn (spectralRaisingCoefficients n j c)=
      ∑pq ∈ c.support, ((Real.sqrt (n*(pq.2 j+1) : ℕ) : ℂ)*c pq) •
        multivariateNormalizedL2 n hn (raiseHermiteIndex j pq).1 (raiseHermiteIndex j pq).2 := by
    unfold spectralRaisingCoefficients finiteHermiteCombination
    rw [Finsupp.apply_linearCombination]
    rw [Finsupp.linearCombination_apply]
    simp only [Function.comp_apply, map_smul, Finsupp.linearCombination_single, one_smul]
    simp only [Finsupp.sum, smul_smul]
    apply Finset.sum_congr rfl
    intro pq hpq
    simp only [hermiteL2Family, multivariateNormalizedL2, mul_comm]
  rw [he, sum_inner, correspondenceOperator_finite_hermite_inner]
  simp only [Finsupp.sum, inner_smul_left, map_mul, Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro pq hpq
  rw [gaussianWeakDbar_hermiteCoefficient hn u D j hu pq,
    gaussianHermiteCoefficient_eq_inner]
  ring

/-- Actual Gaussian dbar-form integration by parts for number polynomials
against every unrestricted ordinary weak-form test. -/
theorem correspondenceOperatorNumber_finite_form {n : ℕ} (hn : 0<n)
    (c : HermiteMultiIndex n→₀ℂ) (w : Lp ℂ 2 (complexGaussianMeasure n))
    (E : Fin n→Lp ℂ 2 (complexGaussianMeasure n))
    (hw : ∀j, IsGaussianWeakDbar n w (E j) j) :
    inner ℂ (finiteGaussianNumberL2 n hn c) w=
      ∑j : Fin n, inner ℂ (finiteDbarComponentL2 n hn c j) (E j) := by
  unfold finiteGaussianNumberL2
  rw [spectralNumberCoefficients_eq_sum]
  have he : finiteHermiteCombination n hn
      (∑j : Fin n, spectralRaisingCoefficients n j (loweredCoefficients n c j))=
      ∑j : Fin n, finiteHermiteCombination n hn
        (spectralRaisingCoefficients n j (loweredCoefficients n c j)) := by
    unfold finiteHermiteCombination
    exact map_sum _ _ _
  rw [he, sum_inner]
  apply Finset.sum_congr rfl
  intro j hj
  exact correspondenceOperator_finite_raising_adjoint hn _ w (E j) j (hw j)
#print axioms correspondenceOperatorNumber_finite_form
end
end GinibrePoincare
