module

public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

@[expose] public section

open MeasureTheory
open scoped InnerProductSpace
namespace GinibrePoincare
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def brownianHouseholder (u : E) : E ≃ₗᵢ[ℝ] E :=
  (Submodule.span ℝ {u}).reflection.trans (LinearIsometryEquiv.neg ℝ)

theorem brownianHouseholder_apply (u v : E) :
    brownianHouseholder u v = v - (2 * (inner ℝ u v / ‖u‖ ^ 2)) • u := by
  change -((Submodule.span ℝ {u}).reflection v) = _
  rw [Submodule.reflection_singleton_apply]
  change -(2 • (inner ℝ u v / ‖u‖ ^ 2) • u - v) = _
  simp only [two_smul, two_mul, add_smul]
  abel

theorem brownianHouseholder_same_norm (x e : E) (he : ‖x‖ = ‖e‖) :
    brownianHouseholder (x-e) x = e := by
  rw [brownianHouseholder_apply]
  by_cases hzero : x-e = 0
  · have hx : x = e := sub_eq_zero.mp hzero
    simp [hx]
  have hnorm : ‖x-e‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hzero)
  have hid : 2 * inner ℝ (x-e) x = ‖x-e‖ ^ 2 := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq, norm_sub_sq_real, ← he, real_inner_comm e x]
    ring
  have hc : 2 * (inner ℝ (x-e) x / ‖x-e‖ ^ 2) = 1 := by
    rw [← mul_div_assoc, hid, div_self hnorm]
  rw [hc, one_smul]
  abel

theorem brownianHouseholder_radial_coordinate (x e v : E) (he : ‖x‖ = ‖e‖) :
    inner ℝ e (brownianHouseholder (x-e) v) = inner ℝ x v := by
  have hh := (brownianHouseholder (x-e)).inner_map_map x v
  rw [brownianHouseholder_same_norm x e he] at hh
  exact hh

theorem brownianHouseholder_measurable [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] :
    Measurable (fun p : E × E => brownianHouseholder p.1 p.2) := by
  simp_rw [brownianHouseholder_apply]
  fun_prop

end
end GinibrePoincare
