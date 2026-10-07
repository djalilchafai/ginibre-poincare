module

public import GinibrePoincare.Analysis.BrownianNullAugmentationIndependence

@[expose] public section

/-! Null augmentation makes every almost-everywhere modification measurable in the same past. -/
open MeasureTheory Filter
namespace GinibrePoincare
noncomputable section

theorem ginibreNullAugmentation_measurable_congr {Ω E : Type*}
    [mAmbient : MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (m : MeasurableSpace Ω) (X Y : Ω → E)
    (hY : @Measurable Ω E (ginibreNullAugmentation (mAmbient := mAmbient) P m) _ Y)
    (hXY : X =ᵐ[P] Y) :
    @Measurable Ω E (ginibreNullAugmentation (mAmbient := mAmbient) P m) _ X := by
  intro s hs
  have hU : P ((X ⁻¹' s) \ (Y ⁻¹' s)) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hXY] with ω hω
    simp only [Set.mem_sdiff,Set.mem_preimage,hω]
    tauto
  have hV : P ((Y ⁻¹' s) \ (X ⁻¹' s)) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hXY] with ω hω
    simp only [Set.mem_sdiff,Set.mem_preimage,hω]
    tauto
  have hu := ginibreNullAugmentation_null_measurable (mAmbient := mAmbient) P m _ hU
  have hv := ginibreNullAugmentation_null_measurable (mAmbient := mAmbient) P m _ hV
  have he : X ⁻¹' s = ((Y ⁻¹' s) \ ((Y ⁻¹' s) \ (X ⁻¹' s))) ∪ ((X ⁻¹' s) \ (Y ⁻¹' s)) := by
    ext ω
    simp only [Set.mem_union,Set.mem_sdiff]
    tauto
  rw [he]
  exact ((hY hs).diff hv).union hu

end
end GinibrePoincare
