module

public import GinibrePoincare.Analysis.GaussianHermiteMoments
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

@[expose] public section

/-! # Euclidean coordinates for complex configurations -/

namespace GinibrePoincare

noncomputable section

/-- Real and imaginary coordinates identify a complex configuration with a
real Euclidean vector. -/
def configurationEuclideanLinearEquiv (n : ℕ) :
    Configuration n ≃ₗ[ℝ] ((Fin n × Fin 2) → ℝ) where
  toFun z := fun ij : Fin n × Fin 2 ↦ ![(z ij.1).re, (z ij.1).im] ij.2
  invFun x i := ⟨x (i, 0), x (i, 1)⟩
  left_inv z := by
    ext i <;> rfl
  right_inv x := by
    ext ⟨i, j⟩
    fin_cases j <;> rfl
  map_add' x y := by
    ext ⟨i, j⟩
    fin_cases j <;> simp
  map_smul' r x := by
    ext ⟨i, j⟩
    fin_cases j <;> simp

/-- The same coordinate identification as a homeomorphic continuous linear
equivalence, hence in particular a measurable equivalence. -/
def configurationEuclideanEquiv (n : ℕ) :
    Configuration n ≃L[ℝ] EuclideanSpace ℝ (Fin n × Fin 2) :=
  (configurationEuclideanLinearEquiv n).toContinuousLinearEquiv.trans
    (EuclideanSpace.equiv (Fin n × Fin 2) ℝ).symm

@[simp] theorem configurationEuclideanEquiv_apply_zero
    (n : ℕ) (z : Configuration n) (i : Fin n) :
    configurationEuclideanEquiv n z (i, 0) = (z i).re := by
  simp [configurationEuclideanEquiv, configurationEuclideanLinearEquiv]

@[simp] theorem configurationEuclideanEquiv_apply_one
    (n : ℕ) (z : Configuration n) (i : Fin n) :
    configurationEuclideanEquiv n z (i, 1) = (z i).im := by
  simp [configurationEuclideanEquiv, configurationEuclideanLinearEquiv]

@[simp] theorem configurationEuclideanEquiv_symm_apply
    (n : ℕ) (x : EuclideanSpace ℝ (Fin n × Fin 2)) (i : Fin n) :
    (configurationEuclideanEquiv n).symm x i =
      ⟨x (i, 0), x (i, 1)⟩ := by
  simp [configurationEuclideanEquiv, configurationEuclideanLinearEquiv]

theorem measurable_configurationEuclideanEquiv (n : ℕ) :
    Measurable (configurationEuclideanEquiv n) :=
  (configurationEuclideanEquiv n).continuous.measurable

theorem measurable_configurationEuclideanEquiv_symm (n : ℕ) :
    Measurable (configurationEuclideanEquiv n).symm :=
  (configurationEuclideanEquiv n).symm.continuous.measurable

theorem real_inner_configurationEuclideanEquiv
    (n : ℕ) (z : Configuration n)
    (x : EuclideanSpace ℝ (Fin n × Fin 2)) :
    inner ℝ (configurationEuclideanEquiv n z) x =
      configurationRealPairing ((configurationEuclideanEquiv n).symm x) z := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  unfold dotProduct configurationRealPairing
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Fin.sum_univ_two]
  simp only [star_trivial]
  rw [configurationEuclideanEquiv_apply_zero,
    configurationEuclideanEquiv_apply_one]
  simp only [configurationEuclideanEquiv_symm_apply]

end
end GinibrePoincare
