module

public import GinibrePoincare.Analysis.LebesgueL2Convolution

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

/-- Applying a continuous linear map to the values commutes with translation. -/
theorem lebesgueL2Translate_map (n : ℕ) (y : Configuration n) (L : V →L[ℝ] W)
    (u : Lp V 2 (volume : Measure (Configuration n))) :
    L.compLpL 2 volume (lebesgueL2Translate n y u) =
      lebesgueL2Translate n y (L.compLpL 2 volume u) := by
  apply Lp.ext
  have he := (eventually_add_right_iff (volume : Measure (Configuration n)) (-y)).mpr
    (L.coeFn_compLpL u)
  filter_upwards [L.coeFn_compLpL (lebesgueL2Translate n y u),
    lebesgueL2Translate_ae n y u,
    lebesgueL2Translate_ae n y (L.compLpL 2 volume u), he] with x hx ht hs he
  simpa only [sub_eq_add_neg] using hx.trans ((congrArg L ht).trans (he.symm.trans hs.symm))

/-- Applying a continuous linear map to the values commutes with bump averaging. -/
theorem lebesgueL2BumpAverage_map (n : ℕ) (φ : ContDiffBump (0 : Configuration n))
    (L : V →L[ℝ] W) (u : Lp V 2 (volume : Measure (Configuration n))) :
    L.compLpL 2 volume (lebesgueL2BumpAverage n φ u) =
      lebesgueL2BumpAverage n φ (L.compLpL 2 volume u) := by
  unfold lebesgueL2BumpAverage
  rw [← (L.compLpL 2 volume).integral_comp_comm
    (integrable_lebesgueL2BumpIntegrand n φ u)]
  simp only [map_smul, lebesgueL2Translate_map]

/-- Every scalar projection of the vector L² average is represented by the
actual convolution of that projection of a compact representative. -/
theorem lebesgueL2BumpAverage_projection_convolution_ae (n : ℕ)
    (φ : ContDiffBump (0 : Configuration n)) (L : V →L[ℝ] ℝ)
    (f : Configuration n → V) (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    (L.compLpL 2 volume (lebesgueL2BumpAverage n φ (hf.toLp f)) :
      Configuration n → ℝ) =ᵐ[volume]
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (L ∘ f)) := by
  have hm : MemLp (L ∘ f) 2 volume := L.comp_memLp' hf
  have he : L.compLpL 2 volume (hf.toLp f) = hm.toLp (L ∘ f) := by
    apply Lp.ext
    filter_upwards [L.coeFn_compLpL (hf.toLp f), hf.coeFn_toLp,
      hm.coeFn_toLp] with x hx hy hz
    simp only [Function.comp_apply] at hz
    rw [hx, hy, hz]
  rw [lebesgueL2BumpAverage_map, he]
  exact lebesgueL2BumpAverage_convolution_ae n φ (L ∘ f) hm
    (hc.comp_left L.map_zero)

end
end GinibrePoincare
