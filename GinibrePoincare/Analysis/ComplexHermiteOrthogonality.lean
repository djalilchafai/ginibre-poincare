module

public import GinibrePoincare.Analysis.MultivariateComplexHermite
public import GinibrePoincare.Analysis.GaussianPolynomialIntegrability

@[expose] public section

/-! # Analytic prerequisites for complex Hermite orthogonality -/

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace GinibrePoincare
namespace ComplexHermite

noncomputable section

/-- Explicit diagonal finite-sum formula for the normalized complex Hermite
polynomial. -/
theorem normalizedEval_eq_sum (n : ℕ) (hn : 0 < n) (p q : ℕ) (z : ℂ) :
    normalizedEval n hn p q z =
      ((oneDimNormalization n p * oneDimNormalization n q : ℝ) : ℂ) *
        ∑ k ∈ Finset.range (min p q + 1),
          (((-((n : ℝ)⁻¹ : ℂ)) ^ k) * (k.factorial : ℂ) *
              (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ)) *
            z ^ (p - k) * (conj z) ^ (q - k) := by
  simp [normalizedEval, normalized, raw, Z, W, Finset.mul_sum]

/-- Every monomial occurring in the diagonal complex-Hermite expansion is
integrable under the matching complex Gaussian coordinate law. -/
theorem integrable_complex_monomial_complexCoordinateGaussianProbability
    (n a b : ℕ) :
    Integrable (fun z : ℂ ↦ z ^ a * (conj z) ^ b)
      (complexCoordinateGaussianProbability n : Measure ℂ) := by
  apply Integrable.mono'
    (integrable_norm_pow_complexCoordinateGaussianProbability n (a + b))
  · fun_prop
  · filter_upwards with z
    simp only [norm_mul, norm_pow, Complex.norm_conj]
    rw [← pow_add]

/-- Each normalized complex Hermite polynomial is integrable under the
matching complex Gaussian coordinate law. -/
theorem integrable_normalizedEval (n : ℕ) (hn : 0 < n) (p q : ℕ) :
    Integrable (normalizedEval n hn p q)
      (complexCoordinateGaussianProbability n : Measure ℂ) := by
  rw [show normalizedEval n hn p q = fun z ↦
      ((oneDimNormalization n p * oneDimNormalization n q : ℝ) : ℂ) *
        ∑ k ∈ Finset.range (min p q + 1),
          (((-((n : ℝ)⁻¹ : ℂ)) ^ k) * (k.factorial : ℂ) *
              (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ)) *
            z ^ (p - k) * (conj z) ^ (q - k) by
    funext z
    exact normalizedEval_eq_sum n hn p q z]
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro k hk
  simpa only [mul_assoc] using
    (integrable_complex_monomial_complexCoordinateGaussianProbability
      n (p - k) (q - k)).const_mul
        (((-((n : ℝ)⁻¹ : ℂ)) ^ k) * (k.factorial : ℂ) *
          (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ))

/-- The degree-zero normalized complex Hermite polynomial has unit norm. -/
theorem normalizedEval_zero_zero_inner (n : ℕ) (hn : 0 < n) :
    ∫ z : ℂ, conj (normalizedEval n hn 0 0 z) *
        normalizedEval n hn 0 0 z
      ∂(complexCoordinateGaussianProbability n : Measure ℂ) = 1 := by
  simp

end
end ComplexHermite
end GinibrePoincare
