module

public import GinibrePoincare.Analysis.HermiteRodriguesIteration

@[expose] public section
open scoped ComplexConjugate ContDiff
namespace GinibrePoincare
namespace ComplexHermite
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem rodrigues_dbar_add {f g : ℂ → ℂ} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (z : ℂ) :
    dbarOnePublic (fun w => f w+g w) z=dbarOnePublic f z+dbarOnePublic g z := by
  change dbarOnePublic (f+g) z = _
  rw [dbarOnePublic,dbarOnePublic,dbarOnePublic,fderiv_add (hf z) (hg z)]
  simp only [add_apply]
  ring

@[simp] theorem rodrigues_dbar_id (z : ℂ) : dbarOnePublic id z = 0 := by
  rw [dbarOnePublic, (hasFDerivAt_id z).fderiv]
  simp

@[simp] theorem rodrigues_dbar_conj (z : ℂ) : dbarOnePublic conj z = 1 := by
  change dbarOnePublic (fun z => Complex.conjCLE z) z = 1
  rw [dbarOnePublic, Complex.conjCLE.fderiv]
  norm_num [Complex.conjCLE_apply]

/-- Diagonal evaluation turns formal differentiation in `W` into the
real-Fréchet Wirtinger derivative. -/
theorem rodrigues_dbar_diagonalEvalPublic (P : Poly) (z : ℂ) :
    dbarOnePublic (diagonalEvalPublic P) z =
      diagonalEvalPublic (MvPolynomial.pderiv (1 : ComplexHermiteIndex) P) z := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      rw [show diagonalEvalPublic (MvPolynomial.C a) = fun _ : ℂ => a by
        funext w
        simp [diagonalEvalPublic]]
      simp [dbarOnePublic, diagonalEvalPublic]
  | add P Q hP hQ =>
      rw [show diagonalEvalPublic (P + Q) = fun z => diagonalEvalPublic P z + diagonalEvalPublic Q z by
        funext w
        simp [diagonalEvalPublic]]
      rw [rodrigues_dbar_add ((contDiff_diagonalEvalPublic P).differentiable (by simp))
        ((contDiff_diagonalEvalPublic Q).differentiable (by simp)), hP, hQ]
      simp [diagonalEvalPublic]
  | mul_X P i hP =>
      by_cases hi : i = (0 : ComplexHermiteIndex)
      · subst i
        rw [show diagonalEvalPublic (P * MvPolynomial.X (0 : ComplexHermiteIndex)) =
            fun z => diagonalEvalPublic P z * id z by
          funext w
          simp [diagonalEvalPublic]]
        rw [dbarOnePublic_mul ((contDiff_diagonalEvalPublic P).differentiable (by simp)) differentiable_id,
          hP, rodrigues_dbar_id]
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
        rw [dbarOnePublic_mul (g := conj) ((contDiff_diagonalEvalPublic P).differentiable (by simp))
          Complex.conjCLE.differentiable, hP, rodrigues_dbar_conj]
        simp [diagonalEvalPublic]
        ring


 theorem rodrigues_dbar_raw (ρ : ℝ) (p q : ℕ) (z : ℂ) :
    dbarOnePublic (eval ρ p q) z = (q:ℂ)*eval ρ p (q-1) z := by
  change dbarOnePublic (diagonalEvalPublic (raw ρ p q)) z = _
  rw [rodrigues_dbar_diagonalEvalPublic,pderiv_W_raw]
  simp [diagonalEvalPublic,eval]

 theorem rodrigues_dbar_weighted_raw (n p q : ℕ) (z : ℂ) :
    dbarOnePublic (fun w => eval ((n:ℝ)⁻¹) p q w*rodriguesGaussian n w) z =
      ((q:ℂ)*eval ((n:ℝ)⁻¹) p (q-1) z-
        (n:ℂ)*z*eval ((n:ℝ)⁻¹) p q z)*rodriguesGaussian n z := by
  have hP : Differentiable ℝ (eval ((n:ℝ)⁻¹) p q) :=
    (contDiff_diagonalEvalPublic (raw ((n:ℝ)⁻¹) p q)).differentiable (by simp)
  have hG := (contDiff_rodriguesGaussian n).differentiable (by simp)
  rw [dbarOnePublic_mul hP hG,rodrigues_dbar_raw,dbarOne_rodriguesGaussian]
  ring

end
end ComplexHermite
end GinibrePoincare
