module

public import GinibrePoincare.Analysis.BrownianStoppingExitMaximalAdaptation

@[expose] public section

/-! The actual canonical maximal Brownian lifetime is a continuous-time stopping time. -/
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

 theorem ginibreBrownianMaximalLifetime_isStoppingTime {Ω : Type*} [mAmbient : MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) :
    IsStoppingTime (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
      (ginibreBrownianMaximalLifetime n α z B) := by
  classical
  intro s
  have hAE₁ := ginibreBrownianFullContinuousNoise_ae n B P hB α
  have hAE₂ := ginibreBrownianFullPastContinuousNoise_ae n B P hB α s
  have hm := ginibreBrownianFamilyPastSpace_le B P (fun i => (hB i).toIsPreBrownianReal) s
  let mPast := ginibreBrownianFamilyPastSpace B s
  let mAug := ginibreNullAugmentation (mAmbient := mAmbient) P mPast
  have hAug := ginibreNullAugmentation_le (mAmbient := mAmbient) P mPast hm
  let μ := P.trim hAug
  haveI : μ.IsComplete := ginibreNullAugmentation_trim_complete (mAmbient := mAmbient) P mPast hm
  let E : Set Ω := {ω | (s : ℝ≥0∞) < ginibreBrownianMaximalLifetime n α z B ω}
  let A : Set Ω := {ω | (s : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α
    (ginibreBrownianFullPastContinuousNoise n B α s ω).val z}
  have hA : @MeasurableSet Ω mAug A := measurableSet_lt measurable_const
    ((ginibreDrivenMaximalLifetime_measurable hn α z).comp
      (ginibreBrownianFullPastContinuousNoise_measurable (mAmbient := mAmbient) n B P hB α s))
  have hInd : @Measurable Ω ℝ mAug _ (A.indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator hA
  have hAE := ginibreNullAugmentation_ae_transfer (mAmbient := mAmbient) P mPast hm _ (hAE₁.and hAE₂)
  have heq : A.indicator (fun _ => (1 : ℝ)) =ᵐ[μ] E.indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [hAE] with ω hω
    let C := ginibreBrownianFullContinuousNoise n B α ω
    let Q := ginibreBrownianFullPastContinuousNoise n B α s ω
    have hi := ginibreDrivenMaximalLifetime_past_invariant (α := α) (z := z)
      Q.val.continuous Q.property C.val.continuous C.property s (by
        intro u hu
        rw [hω.2 u, hω.1 u, min_eq_left hu.2])
    have hmem : ω ∈ A ↔ ω ∈ E := hi
    by_cases ha : ω ∈ A
    · have he := hmem.mp ha
      simp [Set.indicator, ha, he]
    · have he : ω ∉ E := fun he => ha (hmem.mpr he)
      simp [Set.indicator, ha, he]
  have hME := (aemeasurable_iff_measurable (μ := μ)).mp (hInd.aemeasurable.congr heq)
  have hE : @MeasurableSet Ω mAug E := by
    convert hME (isOpen_Ioi.measurableSet : MeasurableSet (Ioi (0 : ℝ))) using 1
    ext ω
    by_cases he : ω ∈ E <;> simp [Set.indicator, he]
  have hevent : {ω | ginibreBrownianMaximalLifetime n α z B ω ≤ (s : ℝ≥0∞)} = Eᶜ := by
    ext ω
    change (ginibreBrownianMaximalLifetime n α z B ω ≤ (s : ℝ≥0∞)) ↔
      ¬ ((s : ℝ≥0∞) < ginibreBrownianMaximalLifetime n α z B ω)
    exact not_lt.symm
  change @MeasurableSet Ω mAug {ω | ginibreBrownianMaximalLifetime n α z B ω ≤ (s : ℝ≥0∞)}
  exact hevent.symm ▸ hE.compl

end
end GinibrePoincare
