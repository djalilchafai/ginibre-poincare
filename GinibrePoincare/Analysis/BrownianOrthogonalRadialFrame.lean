module

public import GinibrePoincare.Analysis.BrownianOrthogonalHouseholder
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def brownianRadialUnitVector (x e : E) : E := by
  classical
  exact if x = 0 then e else ‖x‖⁻¹ • x

theorem brownianRadialUnitVector_norm (x e : E) (he : ‖e‖ = 1) :
    ‖brownianRadialUnitVector x e‖ = 1 := by
  classical
  unfold brownianRadialUnitVector
  split_ifs with hx
  · exact he
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

def brownianRadialFrame (x e : E) : E ≃ₗᵢ[ℝ] E :=
  brownianHouseholder (brownianRadialUnitVector x e - e)

theorem brownianRadialFrame_radial_coordinate (x e v : E) (he : ‖e‖ = 1) :
    inner ℝ e (brownianRadialFrame x e v) = inner ℝ (brownianRadialUnitVector x e) v :=
  brownianHouseholder_radial_coordinate _ e v (by rw [brownianRadialUnitVector_norm x e he, he])

theorem brownianRadialUnitVector_measurable [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (e : E) : Measurable (fun x => brownianRadialUnitVector x e) := by
  classical
  unfold brownianRadialUnitVector
  exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)

theorem brownianRadialFrame_measurable [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (e : E) :
    Measurable (fun p : E × E => brownianRadialFrame p.1 e p.2) := by
  simp_rw [brownianRadialFrame, brownianHouseholder_apply]
  have hw : Measurable (fun p : E × E => brownianRadialUnitVector p.1 e - e) :=
    ((brownianRadialUnitVector_measurable e).comp measurable_fst).sub measurable_const
  exact measurable_snd.sub ((measurable_const.mul
    ((hw.inner measurable_snd).div (hw.norm.pow_const 2))).smul hw)

end
end GinibrePoincare
