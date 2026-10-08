module
public import GinibrePoincare.Analysis.CorrespondenceBrascampLiebGibbs
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
@[expose] public section
open MeasureTheory Measure
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def CorrespondenceBrascampLiebLocallyL2 (f : E → ℝ) : Prop :=
  ∀ K : Set E, IsCompact K → MemLp f 2 (volume.restrict K)

 theorem correspondenceBrascampLieb_localL2_locallyIntegrable
    (f : E → ℝ) (hf : CorrespondenceBrascampLiebLocallyL2 f) : LocallyIntegrable f volume := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  letI : IsFiniteMeasure ((volume : Measure E).restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  exact memLp_one_iff_integrable.mp ((hf K hK).mono_exponent (by norm_num))

 theorem correspondenceBrascampLieb_localL2_compact_multiplier
    (f η : E → ℝ) (hf : CorrespondenceBrascampLiebLocallyL2 f)
    (hη : Continuous η) (hc : HasCompactSupport η) :
    MemLp (fun x => η x*f x) 2 (volume : Measure E) := by
  have ht : MemLp η ⊤ ((volume : Measure E).restrict (tsupport η)) :=
    hη.memLp_top_of_hasCompactSupport hc _
  have hm := ht.fun_mul (r := 2) (hf (tsupport η) hc)
  have hi := (memLp_indicator_iff_restrict hc.measurableSet).mpr hm
  apply hi.ae_eq
  exact ae_of_all volume fun x => by
    by_cases hx : x ∈ tsupport η
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx,image_eq_zero_of_notMem_tsupport hx]

#print axioms correspondenceBrascampLieb_localL2_compact_multiplier
end
end GinibrePoincare
