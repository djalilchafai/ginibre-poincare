module

public import GinibrePoincare.Analysis.MatrixSchurLinearCoordinates

@[expose] public section

open Matrix OrderDual
open scoped Matrix Matrix.Norms.Operator BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev MatrixSkewCoordinates (n : ℕ) := (SchurLowerIndex n → ℂ) × (Fin n → ℝ)

def matrixSkewSubmodule (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) :=
  (schurConjTransposeCLM n + ContinuousLinearMap.id ℝ _).ker

theorem matrixSkewSubmodule_mem (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    A ∈ matrixSkewSubmodule n ↔ Aᴴ = -A := by
  change Aᴴ + A = 0 ↔ Aᴴ = -A
  exact eq_neg_iff_add_eq_zero.symm

def matrixSkewDiagonalCLM (n : ℕ) : (Fin n → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (Complex.I • Matrix.single i i 1)

theorem matrixSkewDiagonalCLM_apply (n : ℕ) (d : Fin n → ℝ) :
    matrixSkewDiagonalCLM n d = Matrix.diagonal (fun i => (d i : ℂ) * Complex.I) := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp [matrixSkewDiagonalCLM, Matrix.sum_apply, Matrix.single_apply, Matrix.diagonal_apply, eq_comm]
  · have hh : ∀ k, ¬(i = k ∧ j = k) := by
      intro k hk
      exact hij (hk.1.trans hk.2.symm)
    simp [matrixSkewDiagonalCLM, Matrix.sum_apply, Matrix.single_apply, Matrix.diagonal_apply,
      eq_comm, hij, hh]

def matrixSkewCoordinateMap (n : ℕ) : MatrixSkewCoordinates n →L[ℝ]
    Matrix (Fin n) (Fin n) ℂ :=
  (schurSkewCLM n).comp (ContinuousLinearMap.fst ℝ _ _) +
    (matrixSkewDiagonalCLM n).comp (ContinuousLinearMap.snd ℝ _ _)

theorem matrixSkewCoordinateMap_apply (n : ℕ) (p : MatrixSkewCoordinates n) :
    matrixSkewCoordinateMap n p = schurSkewCombination p.1 +
      Matrix.diagonal (fun i => (p.2 i : ℂ) * Complex.I) := by
  simp [matrixSkewCoordinateMap, matrixSkewDiagonalCLM_apply, schurSkewCLM_apply]

theorem matrixSkewCoordinateMap_skew (n : ℕ) (p : MatrixSkewCoordinates n) :
    (matrixSkewCoordinateMap n p)ᴴ = -matrixSkewCoordinateMap n p := by
  rw [matrixSkewCoordinateMap_apply, Matrix.conjTranspose_add,
    schurSkewCombination_conjTranspose]
  have hd : (Matrix.diagonal (fun i => (p.2 i : ℂ) * Complex.I))ᴴ =
      -Matrix.diagonal (fun i => (p.2 i : ℂ) * Complex.I) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.diagonal_apply, hij, Ne.symm hij]
  rw [hd, neg_add]

def matrixSkewReadCoordinates (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] MatrixSkewCoordinates n where
  toFun A := (fun p => A (schurLowerRow p) (schurLowerCol p), fun i => (A i i).im)
  map_add' A B := by ext p <;> simp
  map_smul' r A := by ext p <;> simp

theorem matrixSkewCoordinateMap_reconstruct (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : Aᴴ = -A) : matrixSkewCoordinateMap n (matrixSkewReadCoordinates n A) = A := by
  rw [matrixSkewCoordinateMap_apply]
  let x := (matrixSkewReadCoordinates n A).1
  have hlower (i j : Fin n) (hij : j < i) : schurLowerCombination x i j = A i j := by
    let p : SchurLowerIndex n := ⟨toLex (j, toDual i), hij⟩
    simpa [p, schurLowerRow, schurLowerCol, x, matrixSkewReadCoordinates] using
      schurLowerCombination_lowerEntry x p
  ext i j
  change (schurLowerCombination x - (schurLowerCombination x)ᴴ +
    Matrix.diagonal (fun i => ((A i i).im : ℂ) * Complex.I)) i j = A i j
  rw [Matrix.add_apply, Matrix.sub_apply, Matrix.conjTranspose_apply]
  rcases lt_trichotomy i j with hij | hij | hij
  · rw [schurLowerCombination_upperEntries_zero _ i j (le_of_lt hij), hlower j i hij,
      Matrix.diagonal_apply_ne _ (ne_of_lt hij), add_zero, zero_sub]
    have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) hA
    change star (A j i) = -A i j at he
    rw [he, neg_neg]
  · subst j
    rw [schurLowerCombination_upperEntries_zero _ i i le_rfl, star_zero, sub_self,
      zero_add, Matrix.diagonal_apply_eq]
    have he := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i i) hA
    have hre : (A i i).re = 0 := by
      have hh := congrArg Complex.re he
      simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Complex.star_def,
        Complex.conj_re, Complex.neg_re] at hh
      linarith
    apply Complex.ext <;> simp [hre]
  · rw [hlower i j hij, schurLowerCombination_upperEntries_zero _ j i (le_of_lt hij),
      star_zero, sub_zero, Matrix.diagonal_apply_ne _ (ne_of_gt hij), add_zero]

theorem matrixSkewReadCoordinates_map (n : ℕ) (p : MatrixSkewCoordinates n) :
    matrixSkewReadCoordinates n (matrixSkewCoordinateMap n p) = p := by
  rw [matrixSkewCoordinateMap_apply]
  apply Prod.ext
  · funext q
    change (schurLowerCombination p.1 - (schurLowerCombination p.1)ᴴ +
      Matrix.diagonal (fun i => (p.2 i : ℂ) * Complex.I))
        (schurLowerRow q) (schurLowerCol q) = p.1 q
    have hz : schurLowerCombination p.1 (schurLowerCol q) (schurLowerRow q) = 0 :=
      schurLowerCombination_upperEntries_zero _ _ _ (le_of_lt q.property)
    have hd : Matrix.diagonal (fun i => (p.2 i : ℂ) * Complex.I)
        (schurLowerRow q) (schurLowerCol q) = 0 :=
      Matrix.diagonal_apply_ne _ (ne_of_gt q.property)
    rw [Matrix.add_apply, Matrix.sub_apply, Matrix.conjTranspose_apply,
      schurLowerCombination_lowerEntry, hz, star_zero, sub_zero, hd, add_zero]
  · funext i
    change ((schurLowerCombination p.1 - (schurLowerCombination p.1)ᴴ +
      Matrix.diagonal (fun i => (p.2 i : ℂ) * Complex.I)) i i).im = p.2 i
    rw [Matrix.add_apply, Matrix.sub_apply, Matrix.conjTranspose_apply,
      schurLowerCombination_upperEntries_zero _ i i le_rfl, star_zero, sub_self,
      zero_add, Matrix.diagonal_apply_eq]
    simp

def matrixSkewCoordinateEquiv (n : ℕ) : MatrixSkewCoordinates n ≃ₗ[ℝ] matrixSkewSubmodule n :=
  { toFun := fun p => ⟨matrixSkewCoordinateMap n p,
      (matrixSkewSubmodule_mem n _).mpr (matrixSkewCoordinateMap_skew n p)⟩
    invFun := fun A => matrixSkewReadCoordinates n A.val
    left_inv := matrixSkewReadCoordinates_map n
    right_inv := fun A => Subtype.ext (matrixSkewCoordinateMap_reconstruct n A.val
      ((matrixSkewSubmodule_mem n A.val).mp A.property))
    map_add' := fun p q => Subtype.ext ((matrixSkewCoordinateMap n).map_add p q)
    map_smul' := fun r p => Subtype.ext ((matrixSkewCoordinateMap n).map_smul r p) }

#print axioms matrixSkewCoordinateEquiv
#print axioms matrixSkewCoordinateMap_reconstruct
#print axioms matrixSkewCoordinateMap_skew
end
end GinibrePoincare
