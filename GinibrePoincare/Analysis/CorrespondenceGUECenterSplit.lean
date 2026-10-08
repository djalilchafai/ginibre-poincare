module
public import GinibrePoincare.Analysis.CorrespondenceGUECenterGeometry
public import Mathlib.Analysis.InnerProductSpace.ProdL2
@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def gueCenterLine (n : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℝ {gueCenterUnit n}

def gueCenterLineIsometry (n : ℕ) (hn : 0<n) : ℝ ≃ₗᵢ[ℝ] gueCenterLine n where
  toFun t := ⟨t • gueCenterUnit n,by unfold gueCenterLine; exact Submodule.mem_span_singleton.mpr ⟨t,rfl⟩⟩
  invFun v := inner ℝ (gueCenterUnit n) (v : EuclideanSpace ℝ (Fin n))
  left_inv t := by
    change inner ℝ (gueCenterUnit n) (t • gueCenterUnit n)=t
    rw [real_inner_smul_right,real_inner_self_eq_norm_sq,gueCenterUnit_norm hn]
    simp
  right_inv v := by
    obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp v.property
    apply Subtype.ext
    change (inner ℝ (gueCenterUnit n) (v : EuclideanSpace ℝ (Fin n))) • gueCenterUnit n=v
    rw [← ht,real_inner_smul_right,real_inner_self_eq_norm_sq,gueCenterUnit_norm hn]
    simp
  map_add' a b := by apply Subtype.ext; exact add_smul _ _ _
  map_smul' a b := by apply Subtype.ext; exact mul_smul _ _ _
  norm_map' t := by
    change ‖t • gueCenterUnit n‖=‖t‖
    rw [norm_smul,gueCenterUnit_norm hn,mul_one]


def gueCenterSplitEquiv (n : ℕ) (hn : 0<n) : EuclideanSpace ℝ (Fin n) ≃ᵐ
    ℝ×(gueCenterLine n)ᗮ :=
  (gueCenterLine n).orthogonalDecomposition.toMeasurableEquiv.trans
    ((MeasurableEquiv.toLp 2 (gueCenterLine n×(gueCenterLine n)ᗮ)).symm.trans
      ((gueCenterLineIsometry n hn).symm.toMeasurableEquiv.prodCongr (.refl _)))

theorem gueCenterSplit_volume_preserving (n : ℕ) (hn : 0<n) :
    MeasurePreserving (gueCenterSplitEquiv n hn) volume (volume.prod volume) := by
  exact ((gueCenterLineIsometry n hn).symm.measurePreserving.prod (MeasurePreserving.id _)).comp
    ((WithLp.volume_preserving_ofLp (gueCenterLine n) (gueCenterLine n)ᗮ).comp
      (gueCenterLine n).orthogonalDecomposition.measurePreserving)

theorem gueCenterSplitEquiv_symm_apply (n : ℕ) (hn : 0<n) (t : ℝ)
    (y : (gueCenterLine n)ᗮ) :
    (gueCenterSplitEquiv n hn).symm (t,y)=t • gueCenterUnit n+y := rfl

theorem gueCenter_orthogonal (n : ℕ) (y : (gueCenterLine n)ᗮ) :
    inner ℝ (gueCenterUnit n) (y : EuclideanSpace ℝ (Fin n))=0 := by
  exact (Submodule.mem_orthogonal (gueCenterLine n) y).mp y.property (gueCenterUnit n)
    (Submodule.subset_span (by simp))

#print axioms gueCenterSplit_volume_preserving

#print axioms gueCenterLineIsometry
end
end GinibrePoincare
