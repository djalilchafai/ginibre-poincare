module

public import GinibrePoincare.Analysis.GinibreStochasticBrownianFamilyFiltration

@[expose] public section

/-! Genuine null augmentation of the actual joint Brownian past. -/
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

def ginibreNullAugmentation {Ω : Type*} [mAmbient : MeasurableSpace Ω] (P : Measure Ω)
    (m : MeasurableSpace Ω) : MeasurableSpace Ω :=
  m ⊔ MeasurableSpace.generateFrom {s : Set Ω | P s = 0}

theorem ginibreNullAugmentation_base_le {Ω : Type*} [mAmbient : MeasurableSpace Ω] (P : Measure Ω)
    (m : MeasurableSpace Ω) : m ≤ ginibreNullAugmentation (mAmbient := mAmbient) P m := le_sup_left

theorem ginibreNullAugmentation_null_measurable {Ω : Type*} [mAmbient : MeasurableSpace Ω] (P : Measure Ω)
    (m : MeasurableSpace Ω) (s : Set Ω) (hs : P s = 0) :
    @MeasurableSet Ω (ginibreNullAugmentation (mAmbient := mAmbient) P m) s :=
  (show MeasurableSpace.generateFrom {s : Set Ω | P s = 0} ≤ ginibreNullAugmentation (mAmbient := mAmbient) P m from le_sup_right) _ (MeasurableSpace.GenerateMeasurable.basic s hs)

theorem ginibreNullAugmentation_le {Ω : Type*} [mAmbient : MeasurableSpace Ω] (P : Measure Ω) [P.IsComplete]
    (m : MeasurableSpace Ω) (hm : m ≤ mAmbient) :
    ginibreNullAugmentation (mAmbient := mAmbient) P m ≤ mAmbient := by
  apply sup_le hm
  exact MeasurableSpace.generateFrom_le (fun s hs => measurableSet_of_null hs)

theorem ginibreNullAugmentation_trim_complete {Ω : Type*} [mAmbient : MeasurableSpace Ω] (P : Measure Ω) [P.IsComplete]
    (m : MeasurableSpace Ω) (hm : m ≤ mAmbient) :
    (P.trim (ginibreNullAugmentation_le (mAmbient := mAmbient) P m hm)).IsComplete := by
  constructor
  intro s hs
  exact ginibreNullAugmentation_null_measurable (mAmbient := mAmbient) P m s
    (measure_eq_zero_of_trim_eq_zero (ginibreNullAugmentation_le (mAmbient := mAmbient) P m hm) hs)

theorem ginibreNullAugmentation_ae_transfer {Ω : Type*} [mAmbient : MeasurableSpace Ω] (P : Measure Ω) [P.IsComplete]
    (m : MeasurableSpace Ω) (hm : m ≤ mAmbient) (p : Ω → Prop)
    (hp : ∀ᵐ ω ∂P, p ω) : ∀ᵐ ω ∂P.trim (ginibreNullAugmentation_le (mAmbient := mAmbient) P m hm), p ω := by
  rw [ae_iff] at hp ⊢
  rw [trim_measurableSet_eq _ (ginibreNullAugmentation_null_measurable (mAmbient := mAmbient) P m _ hp)]
  exact hp

def ginibreBrownianAugmentedFiltration {Ω ι : Type*} [mAmbient : MeasurableSpace Ω]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) : Filtration ℝ≥0 mAmbient where
  seq s := ginibreNullAugmentation (mAmbient := mAmbient) P (ginibreBrownianFamilyPastSpace B s)
  mono' s t hst := sup_le_sup_right (ginibreBrownianFamilyPastSpace_mono B hst) _
  le' s := ginibreNullAugmentation_le (mAmbient := mAmbient) P _ (ginibreBrownianFamilyPastSpace_le B P hB s)

end
end GinibrePoincare
