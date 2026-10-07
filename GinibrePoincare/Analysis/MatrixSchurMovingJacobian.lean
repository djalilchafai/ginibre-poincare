module

public import GinibrePoincare.Analysis.MatrixSchurUniqueness
public import GinibrePoincare.Analysis.MatrixUnitaryLowerChart

@[expose] public section

open Matrix
open scoped Matrix Matrix.Norms.Operator
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem matrixLowerRead_skew_commutator {n : ℕ} (T K : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0) (hK : Kᴴ = -K) :
    matrixLowerRead n (K * T - T * K) = schurLowerJacobian T *ᵥ matrixLowerRead n K := by
  let c := matrixSkewReadCoordinates n K
  let D := Matrix.diagonal (fun i => (c.2 i : ℂ) * Complex.I)
  have hrec : schurSkewCombination c.1 + D = K := by
    simpa only [matrixSkewCoordinateMap_apply, c, D] using matrixSkewCoordinateMap_reconstruct n K hK
  have hD : ∀ i j, j < i → D i j = 0 := by
    intro i j hij
    exact Matrix.diagonal_apply_ne _ (ne_of_gt hij)
  have hDT := matrix_upper_product D T hD hT
  have hTD := matrix_upper_product T D hT hD
  funext p
  have he : K * T - T * K =
      (schurSkewCombination c.1 * T - T * schurSkewCombination c.1) + (D * T - T * D) := by
    rw [← hrec]
    noncomm_ring
  change (K * T - T * K) (schurLowerRow p) (schurLowerCol p) = _
  have h1 : (D * T) (schurLowerRow p) (schurLowerCol p) = 0 := hDT _ _ p.property
  have h2 : (T * D) (schurLowerRow p) (schurLowerCol p) = 0 := hTD _ _ p.property
  rw [he]
  simp only [Matrix.add_apply, Matrix.sub_apply, h1, h2, sub_self, add_zero]
  exact (schurLowerJacobian_skew_commutator T hT c.1 p).symm

def schurMovingTangent {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (W : (SchurLowerIndex n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :
    SchurCoordinates n →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  let S : SchurCoordinates n →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    W.comp (ContinuousLinearMap.fst ℝ _ _)
  ((ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℂ)).flip T).comp S -
    ((ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℂ)) T).comp S +
      ((schurUpperCLM n).restrictScalars ℝ).comp (ContinuousLinearMap.snd ℝ _ _)

theorem schurMovingTangent_apply {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (W : (SchurLowerIndex n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (p : SchurCoordinates n) :
    schurMovingTangent T W p = W p.1 * T - T * W p.1 + schurUpperCombination p.2 := by
  simp [schurMovingTangent, schurUpperCLM_apply]

def schurMovingJacobian {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (W : (SchurLowerIndex n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :
    SchurCoordinates n →ₗ[ℝ] SchurCoordinates n :=
  schurEntryCoordinates.comp (schurMovingTangent T W).toLinearMap

def schurMovingUpperTangent {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (W : (SchurLowerIndex n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :
    (SchurLowerIndex n → ℂ) →ₗ[ℝ] (SchurUpperIndex n → ℂ) :=
  (LinearMap.snd ℝ _ _).comp ((schurMovingJacobian T W).comp (LinearMap.inl ℝ _ _))

theorem schurMovingJacobian_block {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0)
    (W : (SchurLowerIndex n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (hW : ∀ x, (W x)ᴴ = -W x) :
    schurMovingJacobian T W =
      ((((Matrix.toLin' (schurLowerJacobian T)).restrictScalars ℝ).comp
        ((matrixLowerRead n).comp W).toLinearMap).comp (LinearMap.fst ℝ _ _)).prod
        ((schurMovingUpperTangent T W).comp (LinearMap.fst ℝ _ _) + LinearMap.snd ℝ _ _) := by
  apply LinearMap.ext
  intro p
  apply Prod.ext
  · change matrixLowerRead n (schurMovingTangent T W p) = _
    rw [schurMovingTangent_apply, map_add]
    have hz : matrixLowerRead n (schurUpperCombination p.2) = 0 := by
      funext q
      exact schurUpperCombination_lower_zero _ _ _ q.property
    rw [hz, add_zero, matrixLowerRead_skew_commutator T _ hT (hW p.1)]
    rfl
  · funext q
    change schurMovingTangent T W p q.val.1 q.val.2 =
      schurMovingTangent T W (p.1, 0) q.val.1 q.val.2 + p.2 q
    rw [schurMovingTangent_apply, schurMovingTangent_apply]
    have hz : schurUpperCombination (0 : SchurUpperIndex n → ℂ) = 0 := by
      rw [← schurUpperCLM_apply, map_zero]
    simp [schurUpperCombination_entry, hz]

/-- In a moving unitary frame, the spectral Jacobian is the Vandermonde weight times
an actual real determinant depending only on the unitary frame coordinates. -/
theorem schurMovingJacobian_det {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0)
    (W : (SchurLowerIndex n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (hW : ∀ x, (W x)ᴴ = -W x) :
    (schurMovingJacobian T W).det = vandermondeWeight (fun i => T i i) *
      (((matrixLowerRead n).comp W).toLinearMap).det := by
  rw [schurMovingJacobian_block T hT W hW, real_triangular_prod_det,
    LinearMap.det_comp, schurLowerJacobian_real_det T hT]

#print axioms schurMovingJacobian_det
end
end GinibrePoincare
