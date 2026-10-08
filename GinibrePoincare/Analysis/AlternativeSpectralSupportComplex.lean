module
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Tactic
@[expose] public section
namespace GinibrePoincare
noncomputable section
open Set
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
set_option backward.isDefEq.respectTransparency false

/-- Every off-real parameter of the actual self-adjoint resolvent pencil is
invertible. The conclusion needs no spectral-gap certificate. -/
theorem spectralSupportComplex_pencil_isUnit (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (z : ℂ) (hz : z.im ≠ 0) : IsUnit (1+(z-1) • R) := by
  have hz1 : z-1 ≠ 0 := by
    intro he
    have h := congrArg Complex.im he
    simp at h
    exact hz h
  let w : ℂ := -(z-1)⁻¹
  have hw : w ∉ spectrum ℂ R := by
    intro hs
    have hr := hR.mem_spectrum_eq_re hs
    have he : 1+(z-1)*w=0 := by dsimp [w];field_simp <;> ring
    rw [hr] at he
    have hi := congrArg Complex.im he
    simp [Complex.mul_im] at hi
    have hw0 : w.re = 0 := hi.resolve_left hz
    rw [hw0] at he
    simp at he
  have hu : IsUnit (algebraMap ℂ (H →L[ℂ] H) w - R) := spectrum.notMem_iff.mp hw
  have hs : IsUnit ((z-1) • (algebraMap ℂ (H →L[ℂ] H) w - R)) := by
    simpa only [Units.smul_def,Units.val_mk0] using IsUnit.smul (Units.mk0 (z-1) hz1) hu
  have he : (z-1) • (algebraMap ℂ (H →L[ℂ] H) w - R) = -(1+(z-1) • R) := by
    rw [smul_sub,Algebra.algebraMap_eq_smul_one,smul_smul]
    have hw : (z-1)*w = -1 := by dsimp [w];field_simp <;> ring
    rw [hw]
    simp [sub_eq_add_neg,add_comm]
  rw [he] at hs
  simpa only [neg_neg] using hs.neg

#print axioms spectralSupportComplex_pencil_isUnit
end
end GinibrePoincare
