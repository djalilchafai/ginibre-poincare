module

public import GinibrePoincare.Analysis.MultivariateHermiteIntegrability

@[expose] public section

/-!
# Moment expansion for complex-Hermite orthogonality

This module isolates the exact finite combinatorics produced by the mixed
moments of a rotationally invariant complex Gaussian.  It introduces no
orthogonality assumption: the sole input is the value of every mixed
monomial moment.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace GinibrePoincare
namespace ComplexHermite

noncomputable section

/-- The exact mixed-moment formula for a centered complex Gaussian of
precision `n`. -/
def MixedMomentFormula (n : ℕ) : Prop :=
  ∀ a b : ℕ,
    ∫ z : ℂ, z ^ a * (conj z) ^ b
        ∂(complexCoordinateGaussianProbability n : Measure ℂ) =
      if a = b then (a.factorial : ℂ) * ((n : ℂ)⁻¹) ^ a else 0

/-- Coefficient of the `k`th monomial in the raw Hermite polynomial of
bidegree `(p,q)` and precision `n`. -/
def diagonalRawCoeff (n p q k : ℕ) : ℂ :=
  (-((n : ℝ)⁻¹ : ℂ)) ^ k * (k.factorial : ℂ) *
    (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ)

/-- The explicit finite double sum to which a normalized Hermite inner
product reduces under the mixed-moment formula. -/
def hermiteInnerMomentSum (n p q r s : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (min p q + 1),
    ∑ l ∈ Finset.range (min r s + 1),
      conj (diagonalRawCoeff n p q k) * diagonalRawCoeff n r s l *
        (if (q - k) + (r - l) = (p - k) + (s - l) then
          ((((q - k) + (r - l)).factorial : ℂ) *
            ((n : ℂ)⁻¹) ^ ((q - k) + (r - l)))
        else 0)

/-- Rigorous finite-sum expansion of a normalized one-coordinate Hermite
inner product from the values of all mixed monomial moments. -/
theorem normalizedEval_inner_eq_momentSum_of_mixedMoments
    (n : ℕ) (hn : 0 < n) (hMom : MixedMomentFormula n)
    (p q r s : ℕ) :
    ∫ z : ℂ, conj (normalizedEval n hn p q z) *
        normalizedEval n hn r s z
      ∂(complexCoordinateGaussianProbability n : Measure ℂ) =
      (((oneDimNormalization n p * oneDimNormalization n q : ℝ) : ℂ) *
        ((oneDimNormalization n r * oneDimNormalization n s : ℝ) : ℂ)) *
        hermiteInnerMomentSum n p q r s := by
  rw [show (fun z : ℂ => conj (normalizedEval n hn p q z) *
      normalizedEval n hn r s z) =
      fun z =>
        (((oneDimNormalization n p * oneDimNormalization n q : ℝ) : ℂ) *
          ((oneDimNormalization n r * oneDimNormalization n s : ℝ) : ℂ)) *
          ∑ k ∈ Finset.range (min p q + 1),
            ∑ l ∈ Finset.range (min r s + 1),
              (conj (diagonalRawCoeff n p q k) * diagonalRawCoeff n r s l) *
                (z ^ ((q - k) + (r - l)) *
                  (conj z) ^ ((p - k) + (s - l))) by
    funext z
    rw [normalizedEval_eq_sum, normalizedEval_eq_sum]
    simp only [map_mul, map_sum, map_pow, starRingEnd_apply]
    simp_rw [Finset.mul_sum, Finset.sum_mul, pow_add]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro l hl
    simp [diagonalRawCoeff]
    ring]
  rw [integral_const_mul]
  congr 1
  unfold hermiteInnerMomentSum
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro l hl
      rw [integral_const_mul, hMom]
    · intro l hl
      exact (integrable_complex_monomial_complexCoordinateGaussianProbability n
        ((q - k) + (r - l)) ((p - k) + (s - l))).const_mul _
  · intro k hk
    exact integrable_finsetSum (Finset.range (min r s + 1)) fun l hl =>
      (integrable_complex_monomial_complexCoordinateGaussianProbability n
        ((q - k) + (r - l)) ((p - k) + (s - l))).const_mul _

/-- If the one-coordinate moment sums have been combinatorially evaluated,
the already-proved Fubini factorization immediately yields multivariate
orthogonality.  This theorem records that final tensor-product step. -/
theorem multivariate_orthogonality_of_oneCoordinate
    (n : ℕ) (hn : 0 < n)
    (horth : ∀ p q r s : ℕ,
      ∫ z : ℂ, conj (normalizedEval n hn p q z) *
          normalizedEval n hn r s z
        ∂(complexCoordinateGaussianProbability n : Measure ℂ) =
        if p = r ∧ q = s then 1 else 0)
    (p q r s : Fin n → ℕ) :
    ∫ z, conj (multivariateNormalized n hn p q z) *
        multivariateNormalized n hn r s z ∂complexGaussianMeasure n =
      if p = r ∧ q = s then 1 else 0 := by
  rw [integral_conj_multivariateNormalized_mul_eq_prod]
  simp_rw [horth]
  by_cases hp : p = r
  · subst r
    by_cases hq : q = s
    · subst s
      simp
    · simp only [true_and, if_neg hq]
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hq
      exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)
  · rw [if_neg (by simp [hp])]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hp
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg (by simp [hj]))

end
end ComplexHermite
end GinibrePoincare
