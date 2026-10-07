module

public import GinibrePoincare.Analysis.RadialL2Convolution
public import GinibrePoincare.Analysis.LebesgueL2MollificationMaps

@[expose] public section

/-! # Linear compatibility of ordinary L² mollification

Continuous linear maps of the values commute with translation and normalized
bump averaging. This permits simultaneous mollification of gradient coordinates.
-/

open MeasureTheory Filter
open scoped Topology Convolution
namespace GinibrePoincare
noncomputable section

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

/-- Applying a continuous linear map to the values commutes with bump averaging. -/
theorem radialL2MollifierAverage_map (n : ℕ) (m : ℕ)
    (L : V →L[ℝ] W) (u : Lp V 2 (volume : Measure (Configuration n))) :
    L.compLpL 2 volume (radialL2MollifierAverage n m u) =
      radialL2MollifierAverage n m (L.compLpL 2 volume u) := by
  unfold radialL2MollifierAverage
  rw [← (L.compLpL 2 volume).integral_comp_comm
    (integrable_radialL2MollifierIntegrand n m u)]
  simp only [map_smul, lebesgueL2Translate_map]

/-- Every scalar projection of the vector L² average is represented by the
actual convolution of that projection of a compact representative. -/
theorem radialL2MollifierAverage_projection_convolution_ae (n : ℕ)
    (m : ℕ) (L : V →L[ℝ] ℝ)
    (f : Configuration n → V) (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    (L.compLpL 2 volume (radialL2MollifierAverage n m (hf.toLp f)) :
      Configuration n → ℝ) =ᵐ[volume]
      (radialMollifierKernel n m ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (L ∘ f)) := by
  have hm : MemLp (L ∘ f) 2 volume := L.comp_memLp' hf
  have he : L.compLpL 2 volume (hf.toLp f) = hm.toLp (L ∘ f) := by
    apply Lp.ext
    filter_upwards [L.coeFn_compLpL (hf.toLp f), hf.coeFn_toLp,
      hm.coeFn_toLp] with x hx hy hz
    simp only [Function.comp_apply] at hz
    rw [hx, hy, hz]
  rw [radialL2MollifierAverage_map, he]
  exact radialL2MollifierAverage_convolution_ae n m (L ∘ f) hm
    (hc.comp_left L.map_zero)

end
end GinibrePoincare
