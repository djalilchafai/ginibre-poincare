module

public import GinibrePoincare.Analysis.MatrixSchurFrameDerivative
public import GinibrePoincare.Analysis.MatrixUnitaryVolume

@[expose] public section

open Matrix Filter
open scoped Matrix Matrix.Norms.Operator Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

/-- The actual derivative, read in matrix entry coordinates and in the moving unitary frame. -/
def matrixSchurFrameNormalizedDerivative {n : ℕ}
    (Q : (SchurLowerIndex n → ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (T : Matrix (Fin n) (Fin n) ℂ) (x : SchurLowerIndex n → ℂ)
    (y : SchurUpperIndex n → ℂ) : SchurCoordinates n →ₗ[ℝ] SchurCoordinates n :=
  schurEntryCoordinates.comp
    ((matrixUnitaryConjugation (Q x)ᴴ).comp
      (fderiv ℝ (matrixSchurFrameChart Q T) (x, y))).toLinearMap

theorem matrixSchurFrameNormalizedDerivative_eq {n : ℕ}
    (Q : (SchurLowerIndex n → ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (T : Matrix (Fin n) (Fin n) ℂ) (x : SchurLowerIndex n → ℂ)
    (y : SchurUpperIndex n → ℂ)
    (D : (SchurLowerIndex n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (hQ : HasFDerivAt Q D x) (hunit : ∀ᶠ z in 𝓝 x, Q z ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    matrixSchurFrameNormalizedDerivative Q T x y =
      schurMovingJacobian (T + schurUpperCombination y) (matrixUnitaryConnection (Q x) D) := by
  apply LinearMap.ext
  intro p
  simp only [matrixSchurFrameNormalizedDerivative, schurMovingJacobian,
    LinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  change schurEntryCoordinates (matrixUnitaryConjugation (Q x)ᴴ
    (fderiv ℝ (matrixSchurFrameChart Q T) (x, y) p)) = _
  rw [matrixUnitaryConjugation_apply, Matrix.conjTranspose_conjTranspose]
  change schurEntryCoordinates ((Q x)ᴴ *
    fderiv ℝ (matrixSchurFrameChart Q T) (x, y) p * Q x) =
    schurEntryCoordinates (schurMovingTangent (T + schurUpperCombination y)
      (matrixUnitaryConnection (Q x) D) p)
  rw [matrixSchurFrameChart_normalized_fderiv Q T x p.1 y p.2 D hQ hunit]

theorem matrixSchurFrameNormalizedDerivative_det {n : ℕ}
    (Q : (SchurLowerIndex n → ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : ∀ i j, j < i → T i j = 0)
    (x : SchurLowerIndex n → ℂ) (y : SchurUpperIndex n → ℂ)
    (D : (SchurLowerIndex n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (hQ : HasFDerivAt Q D x) (hunit : ∀ᶠ z in 𝓝 x, Q z ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (matrixSchurFrameNormalizedDerivative Q T x y).det =
      vandermondeWeight (fun i => (T + schurUpperCombination y) i i) *
        (((matrixLowerRead n).comp (matrixUnitaryConnection (Q x) D)).toLinearMap).det := by
  rw [matrixSchurFrameNormalizedDerivative_eq Q T x y D hQ hunit]
  apply schurMovingJacobian_det
  · intro i j hij
    rw [Matrix.add_apply, hT i j hij, schurUpperCombination_lower_zero y i j hij, add_zero]
  · intro v
    exact matrixUnitary_left_derivative_skew hQ hunit v

/-- In fixed entry coordinates the absolute Jacobian has the same Vandermonde factor;
unitary conjugation contributes determinant of absolute value one. -/
theorem matrixSchurFrame_entry_fderiv_abs_det {n : ℕ}
    (Q : (SchurLowerIndex n → ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : ∀ i j, j < i → T i j = 0)
    (x : SchurLowerIndex n → ℂ) (y : SchurUpperIndex n → ℂ)
    (D : (SchurLowerIndex n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (hQ : HasFDerivAt Q D x) (hunit : ∀ᶠ z in 𝓝 x, Q z ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    |(schurEntryCoordinates.comp
        (fderiv ℝ (matrixSchurFrameChart Q T) (x, y)).toLinearMap).det| =
      vandermondeWeight (fun i => (T + schurUpperCombination y) i i) *
        |(((matrixLowerRead n).comp (matrixUnitaryConnection (Q x) D)).toLinearMap).det| := by
  let E := schurEntryCoordinatesEquiv n
  let C := (matrixUnitaryConjugation (Q x)ᴴ).toLinearMap
  let J := schurEntryCoordinates.comp
    (fderiv ℝ (matrixSchurFrameChart Q T) (x, y)).toLinearMap
  let B := E.toLinearMap.comp (C.comp E.symm.toLinearMap)
  have hux : (Q x)ᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    have hh := hunit.self_of_nhds
    have hx : Q x * (Q x)ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hh
    apply Matrix.mem_unitaryGroup_iff'.mpr
    change ((Q x)ᴴ)ᴴ * (Q x)ᴴ = 1
    rw [Matrix.conjTranspose_conjTranspose]
    exact hx
  have hB : |B.det| = 1 := by
    have he : B.det = C.det := LinearMap.det_conj C E
    rw [he]
    exact matrixUnitaryConjugation_abs_det (Q x)ᴴ hux
  have heq : matrixSchurFrameNormalizedDerivative Q T x y = B.comp J := by
    apply LinearMap.ext
    intro p
    change E (C ((fderiv ℝ (matrixSchurFrameChart Q T) (x, y)) p)) =
      E (C (E.symm (E ((fderiv ℝ (matrixSchurFrameChart Q T) (x, y)) p))))
    rw [E.symm_apply_apply]
  have he : |(matrixSchurFrameNormalizedDerivative Q T x y).det| = |J.det| := by
    rw [heq, LinearMap.det_comp, abs_mul, hB, one_mul]
  rw [matrixSchurFrameNormalizedDerivative_det Q T hT x y D hQ hunit,
    abs_mul, abs_of_nonneg (vandermondeWeight_nonneg _)] at he
  exact he.symm

#print axioms matrixSchurFrameNormalizedDerivative_det
#print axioms matrixSchurFrame_entry_fderiv_abs_det
end
end GinibrePoincare
