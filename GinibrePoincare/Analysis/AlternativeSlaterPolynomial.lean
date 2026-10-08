module

public import GinibrePoincare.Analysis.AlternativeSlaterExpansion

@[expose] public section
namespace GinibrePoincare
noncomputable section
open MeasureTheory ComplexHermite
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Repeated orbital labels give the zero determinant. -/
theorem slaterDeterminant_eq_zero_of_repeated {n : ℕ} (hn : 0 < n)
    (pq : HermiteMultiIndex n) {i j : Fin n} (hij : i ≠ j)
    (hp : pq.1 i = pq.1 j) (hq : pq.2 i = pq.2 j) (z : Configuration n) :
    slaterDeterminant hn pq z = 0 := by
  unfold slaterDeterminant
  rw [Matrix.det_zero_of_row_eq hij (by funext k; rw [hp, hq]), mul_zero]

/-- Every Slater polynomial transforms by the permutation sign. -/
theorem slaterDeterminant_permute {n : ℕ} (hn : 0 < n)
    (pq : HermiteMultiIndex n) (σ : ParticlePermutation n) (z : Configuration n) :
    slaterDeterminant hn pq (permute σ z) = permutationSign σ * slaterDeterminant hn pq z := by
  unfold slaterDeterminant
  let M : Matrix (Fin n) (Fin n) ℂ := fun i j => normalizedEval n hn (pq.1 i) (pq.2 i) (z j)
  change (Real.sqrt (slaterMultiplicity n) : ℂ)⁻¹ * (M.submatrix id σ).det =
    permutationSign σ * ((Real.sqrt (slaterMultiplicity n) : ℂ)⁻¹ * M.det)
  rw [Matrix.det_permute']
  simp only [permutationSign]
  ring

/-- Holomorphic polynomial represented by the all-zero antiholomorphic
Slater labels; this is the alternant in (4.5). -/
def slaterHolomorphicPolynomial (n : ℕ) (p : Fin n → ℕ) : ConfigurationPolynomial n :=
  MvPolynomial.C (Real.sqrt (slaterMultiplicity n) : ℂ)⁻¹ *
    Matrix.det (fun i j : Fin n =>
      MvPolynomial.C (oneDimNormalization n (p i) : ℂ) * (MvPolynomial.X j) ^ p i)

theorem eval_slaterHolomorphicPolynomial {n : ℕ} (hn : 0 < n)
    (p : Fin n → ℕ) (z : Configuration n) :
    MvPolynomial.eval z (slaterHolomorphicPolynomial n p) = slaterDeterminant hn (p, 0) z := by
  unfold slaterHolomorphicPolynomial slaterDeterminant
  rw [map_mul, MvPolynomial.eval_C, RingHom.map_det]
  congr 1
  congr 1
  ext i j
  simp [RingHom.mapMatrix_apply, Matrix.map_apply]

theorem slaterHolomorphicPolynomial_alternating (n : ℕ) (hn : 0 < n)
    (p : Fin n → ℕ) : IsAlternatingConfigurationPolynomial (slaterHolomorphicPolynomial n p) := by
  intro σ
  apply MvPolynomial.funext
  intro z
  rw [eval_permuteConfigurationPolynomial, eval_slaterHolomorphicPolynomial hn,
    map_mul, MvPolynomial.eval_C, eval_slaterHolomorphicPolynomial hn,
    slaterDeterminant_permute]

/-- Exact polynomial Vandermonde divisibility (4.6), with a symmetric
holomorphic quotient, for each all-holomorphic Slater determinant. -/
theorem slater_zero_degree_polynomial_division {n : ℕ} (hn : 0 < n)
    (p : Fin n → ℕ) :
    ∃ Q : ConfigurationPolynomial n, IsSymmetricConfigurationPolynomial Q ∧
      ∀ z, slaterDeterminant hn (p, 0) z = vandermonde z * MvPolynomial.eval z Q := by
  obtain ⟨Q, hQ, hfac⟩ := alternating_polynomial_vandermonde_division
    (slaterHolomorphicPolynomial_alternating n hn p)
  refine ⟨Q, hQ, fun z => ?_⟩
  rw [← eval_slaterHolomorphicPolynomial hn, hfac, map_mul, eval_polynomialVandermonde]

/-- A repeated orbital label also vanishes as a concrete Gaussian L² vector. -/
theorem slaterL2_eq_zero_of_repeated {n : ℕ} (hn : 0 < n)
    (pq : HermiteMultiIndex n) {i j : Fin n} (hij : i ≠ j)
    (hp : pq.1 i = pq.1 j) (hq : pq.2 i = pq.2 j) : slaterL2 hn pq = 0 := by
  apply Lp.ext
  filter_upwards [slaterL2_ae hn pq, Lp.coeFn_zero ℂ 2 (complexGaussianMeasure n)] with z hs hz
  rw [hs, hz, slaterDeterminant_eq_zero_of_repeated hn pq hij hp hq z]
  rfl

end
end GinibrePoincare

#print axioms GinibrePoincare.slaterDeterminant_eq_zero_of_repeated
#print axioms GinibrePoincare.slaterDeterminant_permute
#print axioms GinibrePoincare.eval_slaterHolomorphicPolynomial
#print axioms GinibrePoincare.slaterHolomorphicPolynomial_alternating
#print axioms GinibrePoincare.slater_zero_degree_polynomial_division
#print axioms GinibrePoincare.slaterL2_eq_zero_of_repeated
