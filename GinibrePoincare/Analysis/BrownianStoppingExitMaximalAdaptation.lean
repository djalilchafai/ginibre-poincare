module

public import GinibrePoincare.Analysis.BrownianStoppingExitPastNoisePath

@[expose] public section

/-! The actual canonical maximal Brownian-driven solution is strongly adapted. -/
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

 def ginibreBrownianMaximalProcess {Ω : Type*} (n : ℕ) (α : ℝ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : Configuration n :=
  ginibreDrivenMaximalValue n α (ginibreBrownianFullContinuousNoise n B α ω).val z t

 def ginibreBrownianMaximalLifetime {Ω : Type*} (n : ℕ) (α : ℝ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ginibreDrivenMaximalLifetime n α (ginibreBrownianFullContinuousNoise n B α ω).val z

 theorem ginibreBrownianMaximalLifetime_measurable {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) :
    Measurable (ginibreBrownianMaximalLifetime n α z B) :=
  (ginibreDrivenMaximalLifetime_measurable hn α z).comp
    (ginibreBrownianFullContinuousNoise_measurable n B P hB α)

 theorem ginibreBrownianMaximalProcess_stronglyAdapted {Ω : Type*} [mAmbient : MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) :
    StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
      (ginibreBrownianMaximalProcess n α z B) := by
  intro s
  have hAE₁ := ginibreBrownianFullContinuousNoise_ae n B P hB α
  have hAE₂ := ginibreBrownianFullPastContinuousNoise_ae n B P hB α s
  have hm := ginibreBrownianFamilyPastSpace_le B P (fun i => (hB i).toIsPreBrownianReal) s
  let mPast := ginibreBrownianFamilyPastSpace B s
  let mAug := ginibreNullAugmentation (mAmbient := mAmbient) P mPast
  have hAug := ginibreNullAugmentation_le (mAmbient := mAmbient) P mPast hm
  let μ := P.trim hAug
  haveI : μ.IsComplete := ginibreNullAugmentation_trim_complete (mAmbient := mAmbient) P mPast hm
  have hPast : @Measurable Ω (Configuration n) mAug _ (fun ω =>
      ginibreDrivenMaximalValue n α (ginibreBrownianFullPastContinuousNoise n B α s ω).val z s) :=
    (ginibreDrivenMaximalValue_measurable hn α z s).comp
      (ginibreBrownianFullPastContinuousNoise_measurable (mAmbient := mAmbient) n B P hB α s)
  have hAE := ginibreNullAugmentation_ae_transfer (mAmbient := mAmbient) P mPast hm _
    (hAE₁.and hAE₂)
  have heq : (fun ω => ginibreDrivenMaximalValue n α
      (ginibreBrownianFullPastContinuousNoise n B α s ω).val z s) =ᵐ[μ]
      ginibreBrownianMaximalProcess n α z B s := by
    filter_upwards [hAE] with ω hω
    let A := ginibreBrownianFullPastContinuousNoise n B α s ω
    let C := ginibreBrownianFullContinuousNoise n B α ω
    apply ginibreDrivenMaximalValue_past_invariant A.val.continuous A.property C.val.continuous C.property s
    intro u hu
    rw [hω.2 u, hω.1 u, min_eq_left hu.2]
  exact ((aemeasurable_iff_measurable (μ := μ)).mp
    (hPast.aemeasurable.congr heq)).stronglyMeasurable

end
end GinibrePoincare
