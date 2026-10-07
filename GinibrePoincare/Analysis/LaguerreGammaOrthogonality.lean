module

public import GinibrePoincare.Analysis.GeneralizedLaguerre
public import GinibrePoincare.Analysis.GammaPolynomialMoments

@[expose] public section

open Polynomial MeasureTheory ProbabilityTheory
namespace GinibrePoincare.Laguerre
noncomputable section

/-- The Laguerre operator acts linearly on polynomial sums. -/
theorem operator_add (k : ℕ) (P Q : Polynomial ℝ) :
    operator k (P+Q) = operator k P + operator k Q := by
  simp only [operator, derivative_add, mul_add]
  ring

/-- The exact Laguerre operator action on a monomial. -/
theorem operator_monomial (k j : ℕ) (a : ℝ) :
    operator k (monomial j a) =
      monomial (j-1) (a * j * ((k : ℝ)+j-1)) - monomial j (a*j) := by
  cases j with
  | zero => simp [operator]
  | succ j =>
    ext r
    simp only [coeff_operator, coeff_sub, coeff_monomial, Nat.succ_sub_one]
    by_cases hr : r = j
    · subst r; simp; ring
    · by_cases hr' : r = j+1
      · subst r; simp; ring
      · simp [Ne.symm hr, Ne.symm hr']

/-- Symmetry of the Laguerre differential operator under the actual Gamma law. -/
theorem gammaIntegral_operator_symmetric (k : ℕ) (hk : 0 < k) (P Q : Polynomial ℝ) :
    gammaIntegral k hk (operator k P * Q) = gammaIntegral k hk (P * operator k Q) := by
  induction P using Polynomial.induction_on' with
  | add P R hP hR =>
      simp only [operator_add, add_mul, map_add, hP, hR]
  | monomial i a =>
    induction Q using Polynomial.induction_on' with
    | add Q R hQ hR =>
      simp only [operator_add, mul_add, map_add, hQ, hR]
    | monomial j b =>
      rw [operator_monomial, operator_monomial]
      simp only [sub_mul, mul_sub, monomial_mul_monomial, map_sub, gammaIntegral_monomial]
      cases i with
      | zero =>
        cases j with
        | zero => simp
        | succ j =>
          have hm := gammaMoment_succ k j hk
          simp only [Nat.zero_sub, Nat.succ_sub_one, Nat.cast_zero, zero_mul, mul_zero,
            zero_add, Nat.cast_add, Nat.cast_one]
          rw [hm]
          ring
      | succ i =>
        cases j with
        | zero =>
          have hm := gammaMoment_succ k i hk
          simp only [Nat.zero_sub, Nat.succ_sub_one, Nat.cast_zero, zero_mul, mul_zero,
            Nat.add_zero, Nat.cast_add, Nat.cast_one]
          rw [hm]
          ring
        | succ j =>
          have hm := gammaMoment_succ k (i+j+1) hk
          simp only [Nat.succ_sub_one, Nat.cast_add, Nat.cast_one]
          rw [show i+(j+1) = i+j+1 by omega, show i+1+j = i+j+1 by omega,
            show i+1+(j+1) = (i+j+1)+1 by omega, hm]
          push_cast
          ring

/-- Distinct classical Laguerre polynomials are orthogonal for the Gamma law. -/
theorem integral_polynomial_mul_eq_zero (k m l : ℕ) (hk : 0 < k) (hml : m ≠ l) :
    (∫ x : ℝ, (polynomial k m).eval x * (polynomial k l).eval x
      ∂gammaMeasure (k : ℝ) 1) = 0 := by
  have hs := gammaIntegral_operator_symmetric k hk (polynomial k m) (polynomial k l)
  rw [operator_polynomial k m hk, operator_polynomial k l hk] at hs
  have hleft : (-C (m : ℝ) * polynomial k m) * polynomial k l =
      -(m : ℝ) • (polynomial k m * polynomial k l) := by
    simp only [Polynomial.smul_eq_C_mul, C_neg]
    ring
  have hright : polynomial k m * (-C (l : ℝ) * polynomial k l) =
      -(l : ℝ) • (polynomial k m * polynomial k l) := by
    simp only [Polynomial.smul_eq_C_mul, C_neg]
    ring
  rw [hleft, hright, map_smul, map_smul] at hs
  have hne : (m : ℝ) - l ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hml)
  have hzero : ((m : ℝ)-l) * gammaIntegral k hk (polynomial k m * polynomial k l) = 0 := by
    simp only [smul_eq_mul] at hs
    linarith
  have hi := (mul_eq_zero.mp hzero).resolve_left hne
  simpa only [gammaIntegral, LinearMap.coe_mk, AddHom.coe_mk, Polynomial.eval_mul] using hi

/-- Products of Laguerre polynomials are integrable under the actual Gamma law. -/
theorem integrable_polynomial_mul (k m l : ℕ) (hk : 0 < k) :
    Integrable (fun x : ℝ => (polynomial k m).eval x * (polynomial k l).eval x)
      (gammaMeasure (k : ℝ) 1) := by
  simpa only [Polynomial.eval_mul] using
    integrable_polynomial_gamma k hk (polynomial k m * polynomial k l)

end
end GinibrePoincare.Laguerre
