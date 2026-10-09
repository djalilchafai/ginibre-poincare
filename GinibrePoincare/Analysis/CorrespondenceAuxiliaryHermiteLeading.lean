module

public import GinibrePoincare.Analysis.HermiteMonomialSpan

@[expose] public section
open scoped BigOperators
namespace GinibrePoincare.ComplexHermite
noncomputable section

/-- The coefficient of the leading mixed monomial in the raw polynomial is
exactly one, not just a nonzero triangularity certificate. -/
theorem raw_leading_coefficient (ρ : ℝ) (p q : ℕ) :
    (raw ρ p q).coeff
      (Finsupp.single (0 : Fin 2) p + Finsupp.single 1 q) = 1 := by
  classical
  unfold raw
  rw [MvPolynomial.coeff_sum]
  simp only [Z, W, MvPolynomial.X_pow_eq_monomial, MvPolynomial.C_mul_monomial,
    MvPolynomial.monomial_mul, mul_one, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k hk hk0
    have hkbound : k ≤ p ∧ k ≤ q := by
      have h := Finset.mem_range.mp hk
      omega
    have hne : Finsupp.single (0 : Fin 2) (p-k) + Finsupp.single 1 (q-k) ≠
        Finsupp.single (0 : Fin 2) p + Finsupp.single 1 q := by
      intro he
      have h := congrArg (fun a : Fin 2 →₀ ℕ => a 0) he
      simp at h
      omega
    exact if_neg hne
  · simp

/-- Exact leading coefficient of the paper's normalized complex Hermite
polynomial (Appendix B's triangular normalization). -/
theorem normalized_leading_coefficient (n : ℕ) (hn : 0 < n) (p q : ℕ) :
    (normalized n hn p q).coeff
      (Finsupp.single (0 : Fin 2) p + Finsupp.single 1 q) =
      ((oneDimNormalization n p * oneDimNormalization n q : ℝ) : ℂ) := by
  unfold normalized
  rw [MvPolynomial.coeff_C_mul, raw_leading_coefficient, mul_one]

#print axioms raw_leading_coefficient
#print axioms normalized_leading_coefficient
end
end GinibrePoincare.ComplexHermite
