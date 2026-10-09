module
public import GinibrePoincare.Analysis.CorrespondenceGUEBoundedLSI
public import GinibrePoincare.Analysis.CorrespondenceGUEGeometry
@[expose] public section
open MeasureTheory Set
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def gueRealProjection (n : ℕ) (x : EuclideanSpace ℝ (Fin n×Fin 2)) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => x (i, 0))
def gueAuxProjection (n : ℕ) (x : EuclideanSpace ℝ (Fin n×Fin 2)) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => x (i, 1))
def gueOrderedRawDensity (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.exp (-(n : ℝ)/2*‖x‖^2)*∏p∈guePairs n, gueOrderedPairWeight (x p.2-x p.1)

theorem gueSplit_norm_sq (n : ℕ) (x : EuclideanSpace ℝ (Fin n×Fin 2)) :
    ‖x‖^2=‖gueRealProjection n x‖^2+‖gueAuxProjection n x‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq, gueRealProjection, gueAuxProjection]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  rw [Finset.sum_add_distrib]

theorem gueDoubledOrderedDensity_split (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n×Fin 2)) :
    gueDoubledOrderedDensity n x = gueOrderedRawDensity n (gueRealProjection n x)*
      Real.exp (-(n : ℝ)/2*‖gueAuxProjection n x‖^2) := by
  unfold gueDoubledOrderedDensity gueOrderedRawDensity
  rw [gueSplit_norm_sq]
  have he : -(n : ℝ)/2*(‖gueRealProjection n x‖^2+‖gueAuxProjection n x‖^2)=
      -(n : ℝ)/2*‖gueRealProjection n x‖^2+(-(n : ℝ)/2*‖gueAuxProjection n x‖^2) := by ring
  rw [he, Real.exp_add]
  simp only [gueRealProjection]
  ring

#print axioms gueDoubledOrderedDensity_split
end
end GinibrePoincare
