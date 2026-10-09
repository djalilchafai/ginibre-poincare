module

public import GinibrePoincare.Analysis.HermiteRodriguesMultivariate

@[expose] public section
open scoped ComplexConjugate ContDiff BigOperators
namespace GinibrePoincare
namespace ComplexHermite
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem rodrigues_dhol_add {f g : ℂ → ℂ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (z : ℂ) :
    dholOne (fun w => f w+g w) z=dholOne f z+dholOne g z := by
  change dholOne (f+g) z = _
  rw [dholOne, dholOne, dholOne, fderiv_add (hf z) (hg z)]
  simp only [add_apply]
  ring

@[simp] theorem rodrigues_dhol_id (z : ℂ) : dholOne id z = 1 := by
  rw [dholOne, (hasFDerivAt_id z).fderiv]
  norm_num

@[simp] theorem rodrigues_dhol_conj (z : ℂ) : dholOne conj z = 0 := by
  change dholOne (fun z => Complex.conjCLE z) z = 0
  rw [dholOne, Complex.conjCLE.fderiv]
  norm_num [Complex.conjCLE_apply]

/-- Diagonal evaluation turns formal differentiation in `W` into the
real-Fréchet Wirtinger derivative. -/
theorem rodrigues_dhol_diagonalEvalPublic (P : Poly) (z : ℂ) :
    dholOne (diagonalEvalPublic P) z =
      diagonalEvalPublic (MvPolynomial.pderiv (0 : ComplexHermiteIndex) P) z := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      rw [show diagonalEvalPublic (MvPolynomial.C a) = fun _ : ℂ => a by
        funext w
        simp [diagonalEvalPublic]]
      simp [dholOne, diagonalEvalPublic]
  | add P Q hP hQ =>
      rw [show diagonalEvalPublic (P + Q) = fun z => diagonalEvalPublic P z + diagonalEvalPublic Q z by
        funext w
        simp [diagonalEvalPublic]]
      rw [rodrigues_dhol_add ((contDiff_diagonalEvalPublic P).differentiable (by simp))
        ((contDiff_diagonalEvalPublic Q).differentiable (by simp)), hP, hQ]
      simp [diagonalEvalPublic]
  | mul_X P i hP =>
      by_cases hi : i = (0 : ComplexHermiteIndex)
      · subst i
        rw [show diagonalEvalPublic (P * MvPolynomial.X (0 : ComplexHermiteIndex)) =
            fun z => diagonalEvalPublic P z * id z by
          funext w
          simp [diagonalEvalPublic]]
        rw [dholOne_mul ((contDiff_diagonalEvalPublic P).differentiable (by simp)) differentiable_id,
          hP, rodrigues_dhol_id]
        simp [diagonalEvalPublic]
        ring
      · have hi' : i = (1 : ComplexHermiteIndex) := by
          have hne : i.val ≠ 0 := by
            intro hzero
            apply hi
            apply Fin.ext
            simpa using hzero
          apply Fin.ext
          omega
        subst i
        rw [show diagonalEvalPublic (P * MvPolynomial.X (1 : ComplexHermiteIndex)) =
            fun z => diagonalEvalPublic P z * conj z by
          funext w
          simp [diagonalEvalPublic]]
        rw [dholOne_mul (g := conj) ((contDiff_diagonalEvalPublic P).differentiable (by simp))
          Complex.conjCLE.differentiable, hP, rodrigues_dhol_conj]
        simp [diagonalEvalPublic]
        ring


theorem dholOne_normalizedEval (n : ℕ) (hn : 0<n) (p q : ℕ) (z : ℂ) :
    dholOne (normalizedEval n hn p q) z =
      (Real.sqrt (n*p : ℕ) : ℂ)*normalizedEval n hn (p-1) q z := by
  change dholOne (diagonalEvalPublic (normalized n hn p q)) z = _
  rw [rodrigues_dhol_diagonalEvalPublic, pderiv_Z_normalized]
  simp [diagonalEvalPublic, normalizedEval]

/-- Literal holomorphic coordinate lowering for the full normalized tensor family. -/
theorem dholComponent_multivariateNormalized (n : ℕ) (hn : 0<n)
    (p q : Fin n → ℕ) (j : Fin n) (z : Configuration n) :
    dholComponent (multivariateNormalized n hn p q) j z =
      (Real.sqrt (n*p j : ℕ) : ℂ)*multivariateNormalized n hn (lowerAt p j) q z := by
  unfold multivariateNormalized
  rw [dholComponent_tensor _ (fun i => differentiable_normalizedEval n hn (p i) (q i)),
    dholOne_normalizedEval]
  unfold lowerAt
  rw [← Finset.mul_prod_erase Finset.univ
    (fun i => normalizedEval n hn ((Function.update p j (p j-1)) i) (q i) (z i))
    (Finset.mem_univ j)]
  simp only [Function.update_self]
  have hprod : (∏ i∈Finset.univ.erase j, normalizedEval n hn
      (Function.update p j (p j-1) i) (q i) (z i)) =
      ∏ i∈Finset.univ.erase j, normalizedEval n hn (p i) (q i) (z i) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  rw [hprod]
  ring

#print axioms dholComponent_multivariateNormalized

end
end ComplexHermite
end GinibrePoincare
