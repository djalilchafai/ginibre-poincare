module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryRegularizedEuclidean
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Gradient.Basic
@[expose] public section
open Set
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]

lemma bakryEmery_isometry_dual_norm (e : E ≃ₗᵢ[ℝ] F) (L : F →L[ℝ] ℝ) :
    ‖L.comp e.toContinuousLinearEquiv.toContinuousLinearMap‖ = ‖L‖ := by
  apply le_antisymm
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_left e.toLinearIsometry.norm_toContinuousLinearMap_le
        (norm_nonneg L)).trans_eq (mul_one _))
  · apply ContinuousLinearMap.opNorm_le_bound L (norm_nonneg _)
    intro y
    have h := ContinuousLinearMap.le_opNorm (L.comp e.toContinuousLinearEquiv.toContinuousLinearMap) (e.symm y)
    simpa only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.apply_symm_apply,
      LinearIsometryEquiv.norm_map] using h

/-- The literal gradient energy is preserved by real/complex Hilbert
coordinate isometries, including the composed test function derivative. -/
theorem bakryEmery_isometry_gradient_norm (e : E ≃ₗᵢ[ℝ] F) (f : F → ℝ)
    (x : E) (hf : DifferentiableAt ℝ f (e x)) :
    ‖gradient (f ∘ e) x‖ = ‖gradient f (e x)‖ := by
  have hd : fderiv ℝ (f ∘ e) x = (fderiv ℝ f (e x)).comp
      e.toContinuousLinearEquiv.toContinuousLinearMap :=
    (hf.hasFDerivAt.comp x e.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt).fderiv
  simp only [gradient, LinearIsometryEquiv.norm_map]
  rw [hd]
  exact bakryEmery_isometry_dual_norm e _

#print axioms bakryEmery_isometry_dual_norm
#print axioms bakryEmery_isometry_gradient_norm
end
end GinibrePoincare
