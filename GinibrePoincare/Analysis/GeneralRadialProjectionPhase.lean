module

public import GinibrePoincare.Analysis.NonQuadraticBergmanPhase
public import GinibrePoincare.Analysis.GeneralRadialProjectionFourier
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

@[expose] public section

open MeasureTheory Set
open scoped Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The actual pullback action of circle rotations is strongly continuous
on all planar Lebesgue L² vectors. -/
theorem planarLebesguePhase_circle_continuous {T : ℝ} [Fact (0 < T)]
    (u : PlanarLebesgueL2) :
    Continuous (fun t : AddCircle T => planarLebesguePhase (AddCircle.toCircle t)
      (Circle.norm_coe _) u) := by
  let g : AddCircle T → C(ℂ, ℂ) := fun t =>
    ⟨fun z => (AddCircle.toCircle t : ℂ) * z, continuous_const.mul continuous_id⟩
  have hg : Continuous g := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact ((continuous_subtype_val.comp AddCircle.continuous_toCircle).comp continuous_fst).mul continuous_snd
  have hmp : ∀ t, MeasurePreserving (g t) (volume : Measure ℂ) volume := fun t =>
    measurePreserving_complex_mul_of_norm_one _ (Circle.norm_coe _)
  exact continuous_const.compMeasurePreservingLp hg hmp (by norm_num : (2 : ENNReal) ≠ ⊤)

/-- Every actual L² vector is in the closed span of the Fourier modes of
its own continuous rotation orbit. -/
theorem planarLebesgue_mem_closed_span_phase_fourier {T : ℝ} [Fact (0 < T)]
    (u : PlanarLebesgueL2) :
    u ∈ (Submodule.span ℂ (range (fourierCoeff (fun t : AddCircle T =>
      planarLebesguePhase (AddCircle.toCircle t) (Circle.norm_coe _) u)))).topologicalClosure := by
  have h := continuous_circle_mem_closed_span_fourierCoeff _
    (planarLebesguePhase_circle_continuous (T := T) u) 0
  convert h using 1
  simp only [AddCircle.toCircle_zero]
  symm
  simp only [planarLebesguePhase, l2PullbackEquiv, Circle.coe_one]
  change Lp.compMeasurePreserving (complexMulMeasurableEquiv 1 _) _ u = u
  have he : (complexMulMeasurableEquiv 1 (by simp) : ℂ → ℂ) = id := funext one_mul
  simp only [he]
  exact Lp.compMeasurePreserving_id_apply u

end
end GinibrePoincare
