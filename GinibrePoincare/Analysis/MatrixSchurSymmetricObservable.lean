module

public import GinibrePoincare.Analysis.MatrixSchurDiagonalIntegration
public import Mathlib.Topology.Algebra.MvPolynomial

@[expose] public section

open Matrix MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem matrix_charpoly_separable_iff_resultant_ne_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) :
    A.charpoly.Separable ↔ MvPolynomial.eval (fun ij => A ij.1 ij.2)
      (matrixCharacteristicResultant n) ≠ 0 := by
  rw [matrixCharacteristicResultant_eval]
  constructor
  · intro hs hz
    have hr := Polynomial.resultant_eq_zero_iff.mp hz
    exact hr.2 hs
  · intro h
    by_contra hs
    exact h (Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl A.charpoly_monic.ne_zero, hs⟩)

def matrixSimpleSymmetricObservable (n : ℕ) (F : (Fin n → ℂ) → ℝ≥0∞)
    (A : Fin n → Fin n → ℂ) : ℝ≥0∞ := by
  classical
  exact if (Matrix.of A).charpoly.Separable then F (matrixMeasurableEigenvalues n A) else 0


theorem measurableSet_matrixSimpleSpectrum (n : ℕ) :
    MeasurableSet {A : Fin n → Fin n → ℂ | (Matrix.of A).charpoly.Separable} := by
  have he : {A : Fin n → Fin n → ℂ | (Matrix.of A).charpoly.Separable} =
      {A | MvPolynomial.eval (Function.uncurry A) (matrixCharacteristicResultant n) ≠ 0} := by
    ext A
    exact matrix_charpoly_separable_iff_resultant_ne_zero (Matrix.of A)
  rw [he]
  have hm : Measurable (fun A : Fin n → Fin n → ℂ =>
      MvPolynomial.eval (Function.uncurry A) (matrixCharacteristicResultant n)) :=
    (MvPolynomial.continuous_eval (matrixCharacteristicResultant n)).measurable.comp (by fun_prop)
  exact (measurableSet_eq_fun hm measurable_const).compl

theorem matrixSimpleSymmetricObservable_measurable {n : ℕ}
    (F : (Fin n → ℂ) → ℝ≥0∞) (hF : Measurable F) :
    Measurable (matrixSimpleSymmetricObservable n F) := by
  classical
  exact (hF.comp (matrixMeasurableEigenvalues_measurable n)).piecewise
    (measurableSet_matrixSimpleSpectrum n) measurable_const

theorem matrixSimpleSymmetricObservable_unitary {n : ℕ}
    (F : (Fin n → ℂ) → ℝ≥0∞)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z)
    (U A : Matrix (Fin n) (Fin n) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    matrixSimpleSymmetricObservable n F (U * A * Uᴴ) = matrixSimpleSymmetricObservable n F A := by
  classical
  change (if (U * A * Uᴴ).charpoly.Separable then F (matrixMeasurableEigenvalues n (U * A * Uᴴ)) else 0) =
    (if A.charpoly.Separable then F (matrixMeasurableEigenvalues n A) else 0)
  have hc := matrix_charpoly_unitary_conjugation A U hU
  by_cases hs : A.charpoly.Separable
  · have hsU : (U * A * Uᴴ).charpoly.Separable := hc.symm ▸ hs
    rw [if_pos hsU, if_pos hs]
    have h1 := matrixMeasurableEigenvalues_spec n (U * A * Uᴴ) hsU
    have h2 := matrixMeasurableEigenvalues_spec n A hs
    have hr : ∀ i, A.charpoly.eval (matrixMeasurableEigenvalues n (U * A * Uᴴ) i) = 0 := by
      intro i
      rw [← hc]
      exact h1.2 i
    obtain ⟨e, he⟩ := matrixSimpleSpectrum_labels_permutation n A hs
      (matrixMeasurableEigenvalues n A) (matrixMeasurableEigenvalues n (U * A * Uᴴ))
      h2.1 h1.1 h2.2 hr
    have hfun : matrixMeasurableEigenvalues n (U * A * Uᴴ) = matrixMeasurableEigenvalues n A ∘ e :=
      funext he
    rw [hfun, hsym]
  · have hsU : ¬(U * A * Uᴴ).charpoly.Separable := by rw [hc]; exact hs
    rw [if_neg hsU, if_neg hs]

theorem matrixSimpleSymmetricObservable_schurUpper {n : ℕ}
    (F : (Fin n → ℂ) → ℝ≥0∞)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z)
    (y : SchurUpperIndex n → ℂ) (hy : y ∈ matrixSchurSortedUpperDomain n) :
    matrixSimpleSymmetricObservable n F (schurUpperCombination y) =
      F (fun i => schurUpperCombination y i i) := by
  classical
  let A := schurUpperCombination y
  let a := fun i => A i i
  have ha : Function.Injective a := matrixSchurOrderedDiagonal_injective hy
  have hr : ∀ i, A.charpoly.eval (a i) = 0 :=
    schur_diagonal_roots A (fun i j hij => schurUpperCombination_lower_zero y i j hij)
  have hs := matrix_injective_full_roots_separable n A a ha hr
  have hb := matrixMeasurableEigenvalues_spec n A hs
  obtain ⟨e, he⟩ := matrixSimpleSpectrum_labels_permutation n A hs
    a (matrixMeasurableEigenvalues n A) ha hb.1 hr hb.2
  have hf : matrixMeasurableEigenvalues n A = a ∘ e := funext he
  change (if A.charpoly.Separable then F (matrixMeasurableEigenvalues n A) else 0) = F a
  rw [if_pos hs, hf, hsym]

theorem matrixSimpleSymmetricObservable_ae {n : ℕ} (F : (Fin n → ℂ) → ℝ≥0∞) :
    matrixSimpleSymmetricObservable n F =ᵐ[matrixGaussianMeasure n]
      (fun A => F (matrixMeasurableEigenvalues n A)) := by
  classical
  filter_upwards [matrixGaussian_charpoly_separable_ae n] with A hA
  exact if_pos hA

#print axioms matrix_charpoly_separable_iff_resultant_ne_zero
end
end GinibrePoincare
