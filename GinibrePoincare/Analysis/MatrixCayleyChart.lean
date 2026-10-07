module

public import GinibrePoincare.Analysis.MatrixSchurLocalChart
public import Mathlib.Algebra.GroupWithZero.Commute

@[expose] public section

open Matrix NormedSpace Filter
open scoped Topology
open scoped Matrix Matrix.Norms.Operator
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def matrixCayley {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 + K) * (1 - K)⁻¹

theorem matrixCayley_unitary {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ)
    (hsk : Kᴴ = -K) (hden : IsUnit ((1 : Matrix (Fin n) (Fin n) ℂ) - K)) :
    matrixCayley K ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  let X := (1 : Matrix (Fin n) (Fin n) ℂ) + K
  let Y := (1 : Matrix (Fin n) (Fin n) ℂ) - K
  have hy : IsUnit Y := hden
  have hx : IsUnit X := by
    have hh : IsUnit (((1 : Matrix (Fin n) (Fin n) ℂ) - K)ᴴ) := hden.star
    simpa [X, Matrix.conjTranspose_sub, hsk] using hh
  have hdx : IsUnit X.det := (Matrix.isUnit_iff_isUnit_det X).mp hx
  have hdy : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).mp hy
  have hxy : Commute X Y := by
    change (1 + K) * (1 - K) = (1 - K) * (1 + K)
    noncomm_ring
  have hswap : Y⁻¹ * X⁻¹ = X⁻¹ * Y⁻¹ := by
    have hh := hxy.ringInverse_ringInverse.eq
    simpa only [← Matrix.nonsing_inv_eq_ringInverse] using hh.symm
  have hXstar : Xᴴ = Y := by simp [X, Y, hsk, sub_eq_add_neg]
  have hYstar : Yᴴ = X := by simp [X, Y, hsk, sub_eq_add_neg]
  apply Matrix.mem_unitaryGroup_iff.mpr
  change (X * Y⁻¹) * (X * Y⁻¹)ᴴ = 1
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, hXstar, hYstar]
  calc
    _ = X * (Y⁻¹ * X⁻¹) * Y := by noncomm_ring
    _ = (X * X⁻¹) * (Y⁻¹ * Y) := by rw [hswap]; noncomm_ring
    _ = 1 := by rw [Matrix.mul_nonsing_inv X hdx, Matrix.nonsing_inv_mul Y hdy, Matrix.one_mul]

theorem matrixCayley_hasStrictFDerivAt_zero {n : ℕ} :
    HasStrictFDerivAt (matrixCayley : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      ((2 : ℝ) • ContinuousLinearMap.id ℝ _) 0 := by
  let M := Matrix (Fin n) (Fin n) ℂ
  have hi : HasStrictFDerivAt (Ring.inverse : M → M)
      (-ContinuousLinearMap.id ℝ M) 1 := by
    have he : ContinuousLinearMap.mulLeftRight ℝ M 1 1 = ContinuousLinearMap.id ℝ M := by
      apply ContinuousLinearMap.ext
      intro H
      simp [ContinuousLinearMap.mulLeftRight]
    simpa only [Units.val_one, inv_one, he] using
      (hasStrictFDerivAt_ringInverse (𝕜 := ℝ) (1 : Mˣ))
  have hL := (hasStrictFDerivAt_const (𝕜 := ℝ) (1 : M) (0 : M)).add (hasStrictFDerivAt_id (𝕜 := ℝ) (0 : M))
  have hR0 := (hasStrictFDerivAt_const (𝕜 := ℝ) (1 : M) (0 : M)).sub (hasStrictFDerivAt_id (𝕜 := ℝ) (0 : M))
  have hz : ((fun _ : M => (1 : M)) - (id : M → M)) (0 : M) = 1 := by simp
  rw [← hz] at hi
  have hR := hi.comp (0 : M) hR0
  have hd := hL.mul' hR
  let D0 : M →L[ℝ] M :=
    ((1 : M) + 0) • ((-ContinuousLinearMap.id ℝ M).comp (0 - ContinuousLinearMap.id ℝ M)) +
      MulOpposite.op (Ring.inverse ((1 : M) - 0)) • (0 + ContinuousLinearMap.id ℝ M)
  have hD : HasStrictFDerivAt matrixCayley D0 0 := by
    have hf : (matrixCayley : M → M) =
        ((fun _ : M => (1 : M)) + (id : M → M)) * (fun x => Ring.inverse (((fun _ : M => (1 : M)) - (id : M → M)) x)) := by
      funext K
      change (1 + K) * (1 - K)⁻¹ = (1 + K) * Ring.inverse (1 - K)
      rw [Matrix.nonsing_inv_eq_ringInverse]
    rw [hf]
    exact hd
  have he : D0 = (2 : ℝ) • ContinuousLinearMap.id ℝ M := by
    apply ContinuousLinearMap.ext
    intro H
    simp [D0, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mulLeftRight,
      Function.comp_def, Pi.add_def, Pi.sub_def, Pi.mul_def, two_smul]
    exact neg_neg H
  exact he ▸ hD

def matrixInverseCayley {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (U - 1) * (U + 1)⁻¹

theorem matrixInverseCayley_cayley {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ)
    (hden : IsUnit ((1 : Matrix (Fin n) (Fin n) ℂ) - K)) :
    matrixInverseCayley (matrixCayley K) = K := by
  let Y := (1 : Matrix (Fin n) (Fin n) ℂ) - K
  have hdy : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).mp hden
  have hcy : matrixCayley K * Y = 1 + K := by
    change ((1 + K) * Y⁻¹) * Y = 1 + K
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul Y hdy, Matrix.mul_one]
  have hp : (matrixCayley K + 1) * Y = (2 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [Matrix.add_mul, hcy, Matrix.one_mul]
    simp only [Y, two_smul]
    abel
  have hm : (matrixCayley K - 1) * Y = (2 : ℂ) • K := by
    rw [Matrix.sub_mul, hcy, Matrix.one_mul]
    simp only [Y, two_smul]
    abel
  have hi : (matrixCayley K + 1)⁻¹ = (1 / 2 : ℂ) • Y :=
    Matrix.inv_eq_right_inv (by rw [Matrix.mul_smul, hp, smul_smul]; norm_num)
  rw [matrixInverseCayley, hi, Matrix.mul_smul, hm, smul_smul]
  norm_num

theorem matrixCayley_inverseCayley {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hden : IsUnit (U + 1)) : matrixCayley (matrixInverseCayley U) = U := by
  let Y := U + 1
  let K := matrixInverseCayley U
  have hdy : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).mp hden
  have hky : K * Y = U - 1 := by
    change ((U - 1) * Y⁻¹) * Y = U - 1
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul Y hdy, Matrix.mul_one]
  have hm : (1 - K) * Y = (2 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [Matrix.sub_mul, Matrix.one_mul, hky]
    simp only [Y, two_smul]
    abel
  have hp : (1 + K) * Y = (2 : ℂ) • U := by
    rw [Matrix.add_mul, Matrix.one_mul, hky]
    simp only [Y, two_smul]
    abel
  have hi : (1 - K)⁻¹ = (1 / 2 : ℂ) • Y :=
    Matrix.inv_eq_right_inv (by rw [Matrix.mul_smul, hm, smul_smul]; norm_num)
  change (1 + K) * (1 - K)⁻¹ = U
  rw [hi, Matrix.mul_smul, hp, smul_smul]
  norm_num

theorem matrixInverseCayley_skew {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hden : IsUnit (U + 1)) :
    (matrixInverseCayley U)ᴴ = -matrixInverseCayley U := by
  let Y := U + 1
  let K := matrixInverseCayley U
  have hdy : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).mp hden
  have hky : K * Y = U - 1 := by
    change ((U - 1) * Y⁻¹) * Y = U - 1
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul Y hdy, Matrix.mul_one]
  have hyk : Y * K = U - 1 := by
    change Y * ((U - 1) * Y⁻¹) = U - 1
    have hc : Y * (U - 1) = (U - 1) * Y := by dsimp [Y]; noncomm_ring
    rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc, Matrix.mul_nonsing_inv Y hdy, Matrix.mul_one]
  have huu : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have huy : U * Yᴴ = Y := by simp [Y, Matrix.mul_add, huu, add_comm]
  have hh := congrArg Matrix.conjTranspose hky
  have hleft : Y * Kᴴ = -(U - 1) := by
    calc
      _ = U * (Yᴴ * Kᴴ) := by rw [← Matrix.mul_assoc, huy]
      _ = U * (Uᴴ - 1) := by rw [← Matrix.conjTranspose_mul, hh]; simp
      _ = -(U - 1) := by rw [Matrix.mul_sub, huu, Matrix.mul_one]; abel
  have he : Y * Kᴴ = Y * (-K) := by rw [Matrix.mul_neg, hyk, hleft]
  have hc := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => Y⁻¹ * A) he
  simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul Y hdy, Matrix.one_mul] using hc

theorem matrixInverseCayley_hasStrictFDerivAt_one {n : ℕ} :
    HasStrictFDerivAt (matrixInverseCayley : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ _) 1 := by
  let M := Matrix (Fin n) (Fin n) ℂ
  let E : M ≃L[ℝ] M :=
    (LinearEquiv.smulOfNeZero ℝ M (2 : ℝ) (by norm_num)).toContinuousLinearEquiv
  have he : E.toContinuousLinearMap = (2 : ℝ) • ContinuousLinearMap.id ℝ M := by
    apply ContinuousLinearMap.ext
    intro K
    rfl
  have hsi : E.symm.toContinuousLinearMap = (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ M := by
    apply ContinuousLinearMap.ext
    intro K
    simp [E, LinearEquiv.smulOfNeZero, LinearEquiv.smulOfUnit, Units.smul_def, one_div]
  have hf := matrixCayley_hasStrictFDerivAt_zero (n := n)
  rw [← he] at hf
  have hg : ∀ᶠ K : M in 𝓝 0, matrixInverseCayley (matrixCayley K) = K := by
    have ho : IsOpen {K : M | (1 - K).det ≠ 0} := isOpen_ne_fun (by fun_prop) continuous_const
    have hm : (0 : M) ∈ {K : M | (1 - K).det ≠ 0} := by simp
    filter_upwards [ho.mem_nhds hm] with K hK
    apply matrixInverseCayley_cayley
    exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hK)
  have hh := hf.to_local_left_inverse hg
  have hz : matrixCayley (0 : M) = 1 := by simp [matrixCayley]
  rw [hz, hsi] at hh
  exact hh

#print axioms matrixInverseCayley_hasStrictFDerivAt_one
#print axioms matrixInverseCayley_skew
#print axioms matrixCayley_inverseCayley
#print axioms matrixInverseCayley_cayley
#print axioms matrixCayley_hasStrictFDerivAt_zero
#print axioms matrixCayley_unitary
end
end GinibrePoincare
