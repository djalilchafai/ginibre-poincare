module

public import GinibrePoincare.Analysis.MatrixLocalSpectrum

@[expose] public section

/-! # The actual Gaussian matrix spectral pushforward

This constructs the law from the matrix ensemble. Identifying its density with the
Vandermonde density is a separate change-of-variables theorem.
-/
open MeasureTheory Matrix
set_option backward.isDefEq.respectTransparency false
namespace GinibrePoincare
noncomputable section

def matrixMeasurableEigenvalues (n : ℕ) : GinibreMatrixCoordinates n → Fin n → ℂ :=
  (matrix_exists_measurable_simple_labeling n).choose

theorem matrixMeasurableEigenvalues_measurable (n : ℕ) :
    Measurable (matrixMeasurableEigenvalues n) :=
  (matrix_exists_measurable_simple_labeling n).choose_spec.1

theorem matrixMeasurableEigenvalues_spec (n : ℕ) (A : GinibreMatrixCoordinates n)
    (hA : (Matrix.of A).charpoly.Separable) :
    Function.Injective (matrixMeasurableEigenvalues n A) ∧
      ∀ i, (Matrix.of A).charpoly.eval (matrixMeasurableEigenvalues n A i) = 0 :=
  (matrix_exists_measurable_simple_labeling n).choose_spec.2 A hA

def matrixSpectralMeasure (n : ℕ) : Measure (Fin n → ℂ) :=
  (matrixGaussianMeasure n).map (matrixMeasurableEigenvalues n)

instance matrixSpectralMeasure_isProbability (n : ℕ) :
    IsProbabilityMeasure (matrixSpectralMeasure n) := by
  constructor
  rw [matrixSpectralMeasure, Measure.map_apply (matrixMeasurableEigenvalues_measurable n)
    MeasurableSet.univ]
  exact matrixGaussianMeasure_univ n

theorem matrixGaussian_measurable_labels_spec_ae (n : ℕ) :
    ∀ᵐ A ∂matrixGaussianMeasure n, Function.Injective (matrixMeasurableEigenvalues n A) ∧
      ∀ i, (Matrix.of A).charpoly.eval (matrixMeasurableEigenvalues n A i) = 0 := by
  filter_upwards [matrixGaussian_charpoly_separable_ae n] with A hA
  exact matrixMeasurableEigenvalues_spec n A hA

theorem matrixSpectralMeasure_distinct_ae (n : ℕ) :
    ∀ᵐ z ∂matrixSpectralMeasure n, Function.Injective z := by
  rw [matrixSpectralMeasure]
  apply (ae_map_iff (matrixMeasurableEigenvalues_measurable n).aemeasurable
    (by
      have he : {x : Fin n → ℂ | Function.Injective x} =
          ⋂ i : Fin n, ⋂ j : Fin n, {x | i = j ∨ x i ≠ x j} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_iInter, Function.Injective]
        constructor
        · intro h i j
          by_cases hij : i = j
          · exact Or.inl hij
          · exact Or.inr fun heq => hij (h heq)
        · intro h i j heq
          exact (h i j).resolve_right fun hn => hn heq
      rw [he]
      apply MeasurableSet.iInter
      intro i
      apply MeasurableSet.iInter
      intro j
      by_cases hij : i = j
      · simp [hij]
      · have hh : MeasurableSet {x : Fin n → ℂ | x i = x j} := (isClosed_eq
          (show Continuous (fun x : Fin n → ℂ => x i) from continuous_apply i)
          (show Continuous (fun x : Fin n → ℂ => x j) from continuous_apply j)).measurableSet
        simpa only [hij, false_or, Set.compl_setOf] using hh.compl)).2
  filter_upwards [matrixGaussian_measurable_labels_spec_ae n] with A hA
  exact hA.1

#print axioms matrixGaussian_measurable_labels_spec_ae
#print axioms matrixSpectralMeasure_distinct_ae
end
end GinibrePoincare
