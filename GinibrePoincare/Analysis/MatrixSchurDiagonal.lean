module

public import GinibrePoincare.Analysis.MatrixSchurOrderedSlice

@[expose] public section

open Matrix NormedSpace InnerProductSpace
open scoped Matrix Matrix.Norms.Operator
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

theorem matrix_upper_mul_diagonal_entry {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.IsUpperTriangular) (hB : B.IsUpperTriangular) (i : Fin n) :
    (A * B) i i = A i i * B i i := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro j hj hji
    rcases lt_or_gt_of_ne hji with hlt | hgt
    · rw [hA hlt, zero_mul]
    · rw [hB hgt, mul_zero]
  · simp

/-- Gram--Schmidt preserves the ordered eigenvalues on the Schur diagonal. -/
theorem eigenbasis_gramSchmidt_schur_diagonal {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (n : ℕ) (f : E →ₗ[ℂ] E) (b : Module.Basis (Fin n) ℂ E) (eig : Fin n → ℂ)
    (hb : ∀ i, f (b i) = eig i • b i) :
    ∃ o : OrthonormalBasis (Fin n) ℂ E,
      (LinearMap.toMatrix o.toBasis o.toBasis f).IsUpperTriangular ∧
      ∀ i, LinearMap.toMatrix o.toBasis o.toBasis f i i = eig i := by
  classical
  have hdim : Module.finrank ℂ E = Fintype.card (Fin n) := Module.finrank_eq_card_basis b
  let o := gramSchmidtOrthonormalBasis hdim b
  let C := o.toBasis.toMatrix b
  let R := b.toMatrix o.toBasis
  let T := LinearMap.toMatrix o.toBasis o.toBasis f
  have hC : C.IsUpperTriangular := gramSchmidtOrthonormalBasis_inv_isUpperTriangular hdim b
  have hCR : C * R = 1 := by
    change o.toBasis.toMatrix b * b.toMatrix o.toBasis = 1
    rw [Module.Basis.toMatrix_mul_toMatrix, Module.Basis.toMatrix_self]
  have hdet : C.det ≠ 0 := by
    intro hd
    have hh := congrArg Matrix.det hCR
    rw [Matrix.det_mul, hd, zero_mul, Matrix.det_one] at hh
    exact zero_ne_one hh
  letI : Invertible C := Matrix.invertibleOfIsUnitDet C (isUnit_iff_ne_zero.mpr hdet)
  have hR : R.IsUpperTriangular := by
    rw [← Matrix.inv_eq_right_inv hCR]
    exact Matrix.blockTriangular_inv_of_blockTriangular hC
  have hTC : T * C = C * Matrix.diagonal eig := by
    ext i j
    rw [Matrix.mul_diagonal]
    have hh := congrFun (f.toMatrix_mulVec_repr o.toBasis o.toBasis (b j)) i
    change (T *ᵥ o.toBasis.repr (b j)) i = _ at hh
    change (T * C) i j = C i j * eig j
    rw [hb j, map_smul] at hh
    simpa only [T, C, Module.Basis.toMatrix_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, Finsupp.smul_apply, smul_eq_mul,
      mul_comm] using hh
  have hT : T.IsUpperTriangular := by
    have he : T = C * Matrix.diagonal eig * R := by
      calc
        T = T * (C * R) := by rw [hCR, Matrix.mul_one]
        _ = (T * C) * R := by rw [Matrix.mul_assoc]
        _ = C * Matrix.diagonal eig * R := by rw [hTC]
    rw [he]
    exact (hC.mul (Matrix.blockTriangular_diagonal eig)).mul hR
  refine ⟨o, hT, ?_⟩
  intro i
  have hci : C i i ≠ 0 := by
    intro hz
    apply hdet
    rw [Matrix.det_of_isUpperTriangular hC]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hz
  have hi := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i i) hTC
  rw [matrix_upper_mul_diagonal_entry T C hT hC i, Matrix.mul_diagonal] at hi
  apply mul_right_cancel₀ hci
  simpa only [mul_comm] using hi

theorem eigenbasis_exists_unitary_schur_with_diagonal {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (n : ℕ) (f : E →ₗ[ℂ] E) (b : Module.Basis (Fin n) ℂ E) (eig : Fin n → ℂ)
    (hb : ∀ i, f (b i) = eig i • b i) (s : OrthonormalBasis (Fin n) ℂ E) :
    ∃ Q T : Matrix (Fin n) (Fin n) ℂ,
      Q ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ (∀ i j, j < i → T i j = 0) ∧
        (∀ i, T i i = eig i) ∧ LinearMap.toMatrix s.toBasis s.toBasis f = Q * T * Qᴴ := by
  classical
  obtain ⟨o, ho, hdiag⟩ := eigenbasis_gramSchmidt_schur_diagonal n f b eig hb
  let Q := s.toBasis.toMatrix o
  let R := o.toBasis.toMatrix s
  let T := LinearMap.toMatrix o.toBasis o.toBasis f
  have hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ := s.toMatrix_orthonormalBasis_mem_unitary o
  have hQQ : Q * Qᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hQ
  have hRQ : R * Q = 1 := by
    change o.toBasis.toMatrix s.toBasis * s.toBasis.toMatrix o.toBasis = 1
    rw [Module.Basis.toMatrix_mul_toMatrix, Module.Basis.toMatrix_self]
  have hR : R = Qᴴ := by
    calc
      R = R * (Q * Qᴴ) := by rw [hQQ, Matrix.mul_one]
      _ = (R * Q) * Qᴴ := by rw [Matrix.mul_assoc]
      _ = Qᴴ := by rw [hRQ, Matrix.one_mul]
  have he : Q * T * R = LinearMap.toMatrix s.toBasis s.toBasis f := by
    change s.toBasis.toMatrix o.toBasis * T * o.toBasis.toMatrix s.toBasis = _
    simp only [← LinearMap.toMatrix_id_eq_basis_toMatrix]
    unfold T
    rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]
    simp
  refine ⟨Q, T, hQ, ?_, hdiag, ?_⟩
  · intro i j hij
    exact ho hij
  · rw [← hR]
    exact he.symm

#print axioms eigenbasis_exists_unitary_schur_with_diagonal
#print axioms eigenbasis_gramSchmidt_schur_diagonal
end
end GinibrePoincare
