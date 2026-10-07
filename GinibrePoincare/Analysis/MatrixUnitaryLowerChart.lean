module

public import GinibrePoincare.Analysis.MatrixSkewCoordinates
public import GinibrePoincare.Analysis.MatrixSchurLocalChart

@[expose] public section

open Matrix NormedSpace
open scoped Matrix Matrix.Norms.Operator
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def matrixLowerRead (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (SchurLowerIndex n → ℂ) :=
  ((LinearMap.fst ℝ _ _).comp (matrixSkewReadCoordinates n)).toContinuousLinearMap

theorem matrixLowerRead_skew (n : ℕ) (x : SchurLowerIndex n → ℂ) :
    matrixLowerRead n (schurSkewCombination x) = x := by
  have hm : matrixSkewCoordinateMap n (x, 0) = schurSkewCombination x := by
    simp [matrixSkewCoordinateMap, schurSkewCLM_apply]
  have hh := congrArg Prod.fst (matrixSkewReadCoordinates_map n (x, 0))
  rw [hm] at hh
  exact hh

def matrixUnitaryLowerCoordinates (n : ℕ) (x : SchurLowerIndex n → ℂ) : SchurLowerIndex n → ℂ :=
  matrixLowerRead n (exp (schurSkewCombination x))

@[simp] theorem matrixUnitaryLowerCoordinates_zero (n : ℕ) : matrixUnitaryLowerCoordinates n 0 = 0 := by
  simp [matrixUnitaryLowerCoordinates, ← schurSkewCLM_apply, matrixLowerRead,
    matrixSkewReadCoordinates, exp_zero]
  funext p
  have hne : schurLowerRow p ≠ schurLowerCol p := ne_of_gt p.property
  simp only [Matrix.one_apply, hne, ite_false, Pi.zero_apply]

theorem matrixUnitaryLowerCoordinates_hasStrictFDerivAt (n : ℕ) :
    HasStrictFDerivAt (matrixUnitaryLowerCoordinates n)
      (ContinuousLinearMap.id ℝ (SchurLowerIndex n → ℂ)) 0 := by
  let M := Matrix (Fin n) (Fin n) ℂ
  let X := SchurLowerIndex n → ℂ
  have hexp : HasStrictFDerivAt (exp : M → M) (1 : M →L[ℝ] M) 0 := hasStrictFDerivAt_exp_zero
  have hs : schurSkewCLM n (0 : X) = 0 := map_zero _
  rw [← hs] at hexp
  have hh := hexp.comp (0 : X) (schurSkewCLM n).hasStrictFDerivAt
  have hd := (matrixLowerRead n).hasStrictFDerivAt.comp (0 : X) hh
  have he : (matrixLowerRead n).comp ((1 : M →L[ℝ] M).comp (schurSkewCLM n)) =
      ContinuousLinearMap.id ℝ X := by
    apply ContinuousLinearMap.ext
    intro x
    change matrixLowerRead n (schurSkewCLM n x) = x
    rw [schurSkewCLM_apply, matrixLowerRead_skew]
  rw [← he]
  have hf : (matrixUnitaryLowerCoordinates n : X → X) =
      fun x => matrixLowerRead n (exp (schurSkewCLM n x)) := by
    funext x
    rw [matrixUnitaryLowerCoordinates, schurSkewCLM_apply]
  rw [hf]
  exact hd

def matrixUnitaryLowerLocalChart (n : ℕ) :
    OpenPartialHomeomorph (SchurLowerIndex n → ℂ) (SchurLowerIndex n → ℂ) :=
  HasStrictFDerivAt.toOpenPartialHomeomorph (f' := ContinuousLinearEquiv.refl ℝ _)
    (matrixUnitaryLowerCoordinates n) (matrixUnitaryLowerCoordinates_hasStrictFDerivAt n)

theorem matrixUnitaryLowerLocalChart_zero_mem_source (n : ℕ) :
    0 ∈ (matrixUnitaryLowerLocalChart n).source :=
  HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source
    (f' := ContinuousLinearEquiv.refl ℝ _) (matrixUnitaryLowerCoordinates_hasStrictFDerivAt n)

/-- A lower skew exponential in the local coordinate neighborhood can be diagonal
only when the lower coordinates vanish. -/
theorem matrixUnitaryLowerLocalChart_diagonal_iff_zero (n : ℕ)
    (x : SchurLowerIndex n → ℂ) (hx : x ∈ (matrixUnitaryLowerLocalChart n).source)
    (hdiag : ∀ i j, i ≠ j → exp (schurSkewCombination x) i j = 0) : x = 0 := by
  let e := matrixUnitaryLowerLocalChart n
  have he : e x = e 0 := by
    change matrixUnitaryLowerCoordinates n x = matrixUnitaryLowerCoordinates n 0
    rw [matrixUnitaryLowerCoordinates_zero]
    funext p
    exact hdiag _ _ (ne_of_gt p.property)
  exact e.injOn hx (matrixUnitaryLowerLocalChart_zero_mem_source n) he

#print axioms matrixUnitaryLowerLocalChart_diagonal_iff_zero
#print axioms matrixUnitaryLowerCoordinates_hasStrictFDerivAt
end
end GinibrePoincare
