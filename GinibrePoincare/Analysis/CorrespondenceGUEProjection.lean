module
public import GinibrePoincare.Analysis.CorrespondenceGUERealMeasure
@[expose] public section
open MeasureTheory
open scoped BigOperators ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def gueRealProjectionLinear (n : ℕ) :
    EuclideanSpace ℝ (Fin n×Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  ((WithLp.linearEquiv 2 ℝ (Fin n→ℝ)).symm.toLinearMap.comp
    (LinearMap.pi (fun i => (PiLp.proj 2 (fun _ : Fin n×Fin 2 => ℝ) (i,0)).toLinearMap))).toContinuousLinearMap

theorem gueRealProjectionLinear_apply (n : ℕ) (x : EuclideanSpace ℝ (Fin n×Fin 2)) :
    gueRealProjectionLinear n x=gueRealProjection n x := rfl

theorem gueRealProjection_contDiff (n : ℕ) : ContDiff ℝ ∞ (gueRealProjection n) :=
  (gueRealProjectionLinear n).contDiff


theorem gue_gradient_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι) (i : ι) :
    (gradient f x) i=fderiv ℝ f x (EuclideanSpace.basisFun ι ℝ i) := by
  rw [← toDual_gradient]
  simp only [InnerProductSpace.toDual_apply_apply,EuclideanSpace.inner_basisFun_real]

theorem gueRealProjection_basis_real (n : ℕ) (i : Fin n) :
    gueRealProjectionLinear n (EuclideanSpace.basisFun (Fin n×Fin 2) ℝ (i,0))=
      EuclideanSpace.basisFun (Fin n) ℝ i := by
  ext j
  simp [gueRealProjectionLinear,EuclideanSpace.basisFun_apply,PiLp.single_apply]

theorem gueRealProjection_basis_aux (n : ℕ) (i : Fin n) :
    gueRealProjectionLinear n (EuclideanSpace.basisFun (Fin n×Fin 2) ℝ (i,1))=0 := by
  ext j
  simp [gueRealProjectionLinear,EuclideanSpace.basisFun_apply,PiLp.single_apply]

theorem gueRealProjection_gradient_norm_sq (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (x : EuclideanSpace ℝ (Fin n×Fin 2)) :
    ‖gradient (f ∘ gueRealProjection n) x‖^2=‖gradient f (gueRealProjection n x)‖^2 := by
  have hd := (hf.differentiable (by norm_num) (gueRealProjection n x)).hasFDerivAt.comp x
    (gueRealProjectionLinear n).hasFDerivAt
  have he : fderiv ℝ (f ∘ gueRealProjection n) x =
      (fderiv ℝ f (gueRealProjection n x)).comp (gueRealProjectionLinear n) := hd.fderiv
  simp only [EuclideanSpace.real_norm_sq_eq]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two,gue_gradient_coordinate,he,ContinuousLinearMap.comp_apply,
    gueRealProjection_basis_real,gueRealProjection_basis_aux,map_zero,zero_pow (by decide : 2≠0),add_zero]

#print axioms gueRealProjection_gradient_norm_sq

#print axioms gueRealProjection_contDiff
end
end GinibrePoincare
