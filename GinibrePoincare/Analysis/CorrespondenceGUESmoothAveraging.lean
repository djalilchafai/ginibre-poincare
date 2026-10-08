module
public import GinibrePoincare.Analysis.CorrespondenceGUEPermutationMeasure
@[expose] public section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def gueSmoothAverage (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (Fintype.card (Equiv.Perm (Fin n)):ℝ)⁻¹*∑σ : Equiv.Perm (Fin n),f (guePermute n σ x)

theorem gueSmoothAverage_symmetric (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (τ : Equiv.Perm (Fin n)) (x : EuclideanSpace ℝ (Fin n)) :
    gueSmoothAverage n f (guePermute n τ x)=gueSmoothAverage n f x := by
  unfold gueSmoothAverage
  simp_rw [guePermute_mul]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ => f (guePermute n σ x))

theorem gueSmoothAverage_contDiff (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (gueSmoothAverage n f) := by
  apply ContDiff.mul contDiff_const
  apply ContDiff.sum
  intro σ hσ
  exact hf.comp (guePermuteIsometry n σ).contDiff

theorem gueSmoothAverage_compact (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : HasCompactSupport f) : HasCompactSupport (gueSmoothAverage n f) := by
  have hsum (s : Finset (Equiv.Perm (Fin n))) : HasCompactSupport (fun x => ∑σ∈s,f (guePermute n σ x)) := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      change HasCompactSupport (0 : EuclideanSpace ℝ (Fin n)→ℝ)
      exact HasCompactSupport.zero
    | @insert σ s hσ ih =>
      simp_rw [Finset.sum_insert hσ]
      exact (hf.comp_homeomorph (guePermuteIsometry n σ).toHomeomorph).add ih
  exact (hsum Finset.univ).mul_left

theorem gueSmoothAverage_eq_of_symmetric (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀σ x,f (guePermute n σ x)=f x) : gueSmoothAverage n f=f := by
  funext x
  unfold gueSmoothAverage
  simp_rw [hf]
  have hc : (Fintype.card (Equiv.Perm (Fin n)):ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [← mul_assoc,inv_mul_cancel₀ hc,one_mul]

theorem guePermute_gradient (n : ℕ) (σ : Equiv.Perm (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (x : EuclideanSpace ℝ (Fin n)) :
    gradient (f ∘ guePermute n σ) x=guePermute n σ.symm (gradient f (guePermute n σ x)) := by
  have hd := (hf.differentiable (by norm_num) (guePermute n σ x)).hasFDerivAt.comp x
    (guePermuteIsometry n σ).toContinuousLinearEquiv.hasFDerivAt
  apply PiLp.ext
  intro i
  rw [gue_gradient_coordinate,hd.fderiv,ContinuousLinearMap.comp_apply]
  have he := congrArg (fderiv ℝ f (guePermute n σ x)) (guePermute_basis n σ i)
  exact he.trans (gue_gradient_coordinate f (guePermute n σ x) (σ.symm i)).symm

theorem gueSmoothAverage_gradient (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ ∞ f) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (gueSmoothAverage n f) x=
      (Fintype.card (Equiv.Perm (Fin n)):ℝ)⁻¹ •∑σ : Equiv.Perm (Fin n),
        guePermute n σ.symm (gradient f (guePermute n σ x)) := by
  have hd σ := (hf.differentiable (by simp) (guePermute n σ x)).hasFDerivAt.comp x
    (guePermuteIsometry n σ).toContinuousLinearEquiv.hasFDerivAt
  have hs := (HasFDerivAt.fun_sum (u := Finset.univ) (fun σ hσ => hd σ)).const_mul
    (Fintype.card (Equiv.Perm (Fin n)):ℝ)⁻¹
  simp only [Function.comp_apply] at hs
  unfold gradient gueSmoothAverage
  rw [hs.fderiv,map_smul,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ hσ
  have hgrad := guePermute_gradient n σ f (hf.of_le (by simp)) x
  unfold gradient at hgrad
  rw [(hd σ).fderiv] at hgrad
  exact hgrad

#print axioms gueSmoothAverage_gradient
end
end GinibrePoincare
