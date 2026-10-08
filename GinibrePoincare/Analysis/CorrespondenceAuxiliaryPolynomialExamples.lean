module

public import GinibrePoincare.Analysis.PolynomialEigenfunctions

@[expose] public section

/-! Literal degree-two identifications in equation (1.35) of arXiv:2608.19358v2.
These identify the actual Hermite–Laguerre family, rather than merely defining
functions with the desired formulas. -/

open scoped ComplexConjugate
namespace GinibrePoincare
noncomputable section

@[simp] theorem polynomialEigenfunction_second_holomorphic (n : ℕ)
    (z : Configuration n) :
    polynomialEigenfunction n ⟨2, 0, 0⟩ z = P_200 z := by
  simp [polynomialEigenfunction, P_200, ComplexHermite.oneDimNormalization,
    Nat.factorial, div_eq_mul_inv, mul_comm]

@[simp] theorem polynomialEigenfunction_second_antiholomorphic (n : ℕ)
    (z : Configuration n) :
    polynomialEigenfunction n ⟨0, 2, 0⟩ z = P_020 z := by
  simp [polynomialEigenfunction, P_020, ComplexHermite.oneDimNormalization,
    Nat.factorial, div_eq_mul_inv, mul_comm]

@[simp] theorem polynomialEigenfunction_first_mixed (n : ℕ)
    (z : Configuration n) :
    polynomialEigenfunction n ⟨1, 1, 0⟩ z = P_110 z := by
  simp [polynomialEigenfunction, P_110, ComplexHermite.normalizedEval,
    ComplexHermite.normalized, ComplexHermite.oneDimNormalization,
    ComplexHermite.raw_one_one, ComplexHermite.Z, ComplexHermite.W,
    Complex.mul_conj]

end
end GinibrePoincare

#print axioms GinibrePoincare.polynomialEigenfunction_second_holomorphic
#print axioms GinibrePoincare.polynomialEigenfunction_second_antiholomorphic
#print axioms GinibrePoincare.polynomialEigenfunction_first_mixed
