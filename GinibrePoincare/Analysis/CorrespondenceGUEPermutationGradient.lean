module
public import GinibrePoincare.Analysis.CorrespondenceGUEFullMeasure
@[expose] public section
open MeasureTheory
open scoped BigOperators ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem guePermute_basis (n : ℕ) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    guePermuteIsometry n σ (EuclideanSpace.basisFun (Fin n) ℝ i)=
      EuclideanSpace.basisFun (Fin n) ℝ (σ.symm i) := by
  ext j
  simp only [guePermuteIsometry_apply,guePermute,EuclideanSpace.basisFun_apply]
  change (Pi.single i (1:ℝ) : Fin n→ℝ) (σ j)=(Pi.single (σ.symm i) 1 : Fin n→ℝ) j
  by_cases h : j=σ.symm i
  · subst j
    simp
  · have hi : σ j≠i := fun he => h (σ.injective (he.trans (σ.apply_symm_apply i).symm))
    simp [Pi.single,Function.update_apply,h,hi]

theorem gueSymmetric_gradient_norm_sq (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (hs : ∀σ x,f (guePermute n σ x)=f x) (σ : Equiv.Perm (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖gradient f (guePermute n σ x)‖^2=‖gradient f x‖^2 := by
  have he : f ∘ guePermute n σ=f := funext (hs σ)
  have hd := (hf.differentiable (by norm_num) (guePermute n σ x)).hasFDerivAt.comp x
    (guePermuteIsometry n σ).toContinuousLinearEquiv.hasFDerivAt
  have hder : (fderiv ℝ f (guePermute n σ x)).comp
      (guePermuteIsometry n σ).toContinuousLinearEquiv.toContinuousLinearMap=fderiv ℝ f x := by
    rw [← hd.fderiv,he]
  have hc (i : Fin n) : (gradient f x) i=(gradient f (guePermute n σ x)) (σ.symm i) := by
    rw [gue_gradient_coordinate,gue_gradient_coordinate,← hder,ContinuousLinearMap.comp_apply]
    exact congrArg (fderiv ℝ f (guePermute n σ x)) (guePermute_basis n σ i)
  simp only [EuclideanSpace.real_norm_sq_eq]
  simp_rw [hc]
  exact (Equiv.sum_comp σ.symm (fun i => (gradient f (guePermute n σ x) i)^2)).symm

#print axioms gueSymmetric_gradient_norm_sq
end
end GinibrePoincare
