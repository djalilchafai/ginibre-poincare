module

public import GinibrePoincare.Analysis.MatrixGaussianMeasure
public import GinibrePoincare.Analysis.MatrixPolynomialNull
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.FieldTheory.Separable

@[expose] public section

/-! # Almost sure simplicity of the complex Ginibre matrix spectrum

The resultant of the characteristic polynomial and its derivative is a
nonzero polynomial in the entries, hence vanishes only on a Gaussian-null
set. Separability expresses simplicity without selecting eigenvalue labels.
-/
open scoped BigOperators
open MeasureTheory Matrix Polynomial

namespace GinibrePoincare
noncomputable section

def matrixCharacteristicResultant (n : ℕ) : MvPolynomial (Fin n × Fin n) ℂ :=
  let p := Matrix.charpoly.univ ℂ (Fin n)
  Polynomial.resultant p p.derivative n (n - 1)

theorem matrixCharacteristicResultant_eval (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial.eval (fun ij => G ij.1 ij.2) (matrixCharacteristicResultant n) =
      Polynomial.resultant G.charpoly G.charpoly.derivative := by
  unfold matrixCharacteristicResultant
  rw [← Polynomial.resultant_map_map]
  have hc : (Matrix.charpoly.univ ℂ (Fin n)).map
      (MvPolynomial.eval (fun ij => G ij.1 ij.2)) = G.charpoly := by
    change (Matrix.charpoly.univ ℂ (Fin n)).map
      (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun ij => G ij.1 ij.2)) = G.charpoly
    exact Matrix.charpoly.univ_map_eval₂Hom (Fin n) (RingHom.id ℂ)
      (fun ij => G ij.1 ij.2)
  rw [← Polynomial.derivative_map, hc]
  simp only [Polynomial.natDegree_derivative, Matrix.charpoly_natDegree_eq_dim,
    Fintype.card_fin]

theorem matrixCharacteristicResultant_ne_zero (n : ℕ) :
    matrixCharacteristicResultant n ≠ 0 := by
  let D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun i => (i.val : ℂ))
  have hsep : D.charpoly.Separable := by
    rw [Matrix.charpoly_diagonal]
    apply Polynomial.separable_prod_X_sub_C_iff.mpr
    intro i j hij
    apply Fin.ext
    change (i.val : ℂ) = (j.val : ℂ) at hij
    exact_mod_cast hij
  have hres := Polynomial.resultant_ne_zero D.charpoly D.charpoly.derivative hsep
  intro hzero
  apply hres
  rw [← matrixCharacteristicResultant_eval n D, hzero, map_zero]

/-- No nonzero entry polynomial vanishes with positive matrix Gaussian probability. -/
theorem matrixGaussian_polynomial_ne_zero_ae {n : ℕ} (hn : 0 < n)
    (p : MvPolynomial (Fin n × Fin n) ℂ) (hp : p ≠ 0) :
    ∀ᵐ G ∂matrixGaussianMeasure n, MvPolynomial.eval (fun ij => G ij.1 ij.2) p ≠ 0 := by
  let μ : Measure ℂ := complexCoordinateGaussianProbability n
  have hμ : μ = (volume : Measure ℂ).withDensity (complexCoordinateGaussianDensity n) :=
    complexCoordinateGaussianMeasure_eq_withDensity hn
  letI : NullSingletonClass μ := by rw [hμ]; infer_instance
  exact (matrixGaussianMeasure_uncurry_preserving n).quasiMeasurePreserving.ae
    (complexMvPolynomial_eval_ne_zero_ae μ p hp)

/-- The actual Gaussian random matrix has a separable characteristic polynomial
almost surely, equivalently its complex spectrum consists of simple roots. -/
theorem matrixGaussian_charpoly_separable_ae (n : ℕ) :
    ∀ᵐ G ∂matrixGaussianMeasure n, G.charpoly.Separable := by
  by_cases hn : 0 < n
  · filter_upwards [matrixGaussian_polynomial_ne_zero_ae hn
      (matrixCharacteristicResultant n) (matrixCharacteristicResultant_ne_zero n)] with G hG
    rw [matrixCharacteristicResultant_eval] at hG
    by_contra hs
    apply hG
    exact Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl G.charpoly_monic.ne_zero, hs⟩
  · have hz : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    filter_upwards with G
    simp [Matrix.charpoly, Polynomial.separable_one]

#print axioms matrixCharacteristicResultant_ne_zero
#print axioms matrixGaussian_charpoly_separable_ae

end
end GinibrePoincare
