module

public import GinibrePoincare.Analysis.BrownianStoppingExitNoisePath
public import GinibrePoincare.Analysis.GinibreStochasticPastAugmentation

@[expose] public section

/-! The actual Brownian past is measurable in its genuine null-augmented filtration. -/
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def ginibreBrownianFullPastRawPath {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ) (s : ℝ≥0) (ω : Ω) :
    C(ℝ, Configuration n) :=
  ContinuousMap.mkD (fun t => ginibreConfigurationBrownianNoise n B α ω (min t (s : ℝ))) 0

theorem ginibreBrownianFullPastRawPath_ae {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsBrownianReal (B i) P) (α : ℝ) (s : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ,
      ginibreBrownianFullPastRawPath n B α s ω t =
        ginibreConfigurationBrownianNoise n B α ω (min (t : ℝ) (s : ℝ)) := by
  filter_upwards [ginibreConfigurationBrownianNoise_actual n B P hB α] with ω hω
  intro t
  have hc : Continuous (fun t : ℝ => ginibreConfigurationBrownianNoise n B α ω (min (t : ℝ) (s : ℝ))) :=
    hω.1.comp (continuous_id.min continuous_const)
  simp [ginibreBrownianFullPastRawPath, ContinuousMap.mkD, hc]

theorem ginibreBrownianFullPastRawPath_measurable {Ω : Type*} [mAmbient : MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (α : ℝ) (s : ℝ≥0) :
    @Measurable _ _ (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) s)
      (borel C(ℝ, Configuration n)) (ginibreBrownianFullPastRawPath n B α s) := by
  letI : MeasurableSpace C(ℝ, Configuration n) := borel _
  letI : BorelSpace C(ℝ, Configuration n) := ⟨rfl⟩
  let hpre := fun i => (hB i).toIsPreBrownianReal
  have hm0 := ginibreBrownianFamilyPastSpace_le B P hpre s
  have hAdapt0 := ginibreBrownianFamilyFiltration_coordinate_stronglyAdapted B P hpre
  have hAEPath := ginibreBrownianFullPastRawPath_ae n B P hB α s
  let mPast := ginibreBrownianFamilyPastSpace B s
  let mAug := ginibreNullAugmentation (mAmbient := mAmbient) P mPast
  have hm : mPast ≤ mAmbient := hm0
  have hAug := ginibreNullAugmentation_le (mAmbient := mAmbient) P mPast hm
  let μ := P.trim hAug
  haveI : μ.IsComplete := ginibreNullAugmentation_trim_complete (mAmbient := mAmbient) P mPast hm
  apply ginibre_measurable_continuousMap_of_evaluations (mΩ := mAug)
  intro t
  apply (aemeasurable_iff_measurable (μ := μ)).mp
  let v : ℝ≥0 := (min (t : ℝ) (s : ℝ)).toNNReal
  have hvs : v ≤ s := by
    dsimp [v]
    exact Real.toNNReal_le_iff_le_coe.mpr (min_le_right _ _)
  have hCoord (i : Fin n × Fin 2) : @Measurable Ω ℝ mAug _ (B i v) := by
    have h := (hAdapt0 i v).measurable
    exact h.mono ((ginibreBrownianFamilyPastSpace_mono B hvs).trans
      (ginibreNullAugmentation_base_le (mAmbient := mAmbient) P mPast)) le_rfl
  have hNoise : @Measurable Ω (Configuration n) mAug _
      (fun ω => ginibreConfigurationBrownianNoise n B α ω (min (t : ℝ) (s : ℝ))) := by
    apply measurable_pi_lambda
    intro j
    exact ((hCoord (j, 0)).complex_ofReal.add
      (measurable_const.mul (hCoord (j, 1)).complex_ofReal)).const_smul (Real.sqrt (2*α/(n : ℝ)^2))
  apply hNoise.aemeasurable.congr
  have hAE := ginibreNullAugmentation_ae_transfer (mAmbient := mAmbient) P mPast hm _
    hAEPath
  filter_upwards [hAE] with ω hω
  exact (hω t).symm

 def ginibreBrownianFullPastContinuousNoise {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ) (s : ℝ≥0) (ω : Ω) : GinibreContinuousNoise n :=
  ginibreContinuousNoiseNormalize n (ginibreBrownianFullPastRawPath n B α s ω)

 theorem ginibreBrownianFullPastContinuousNoise_ae {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsBrownianReal (B i) P) (α : ℝ) (s : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, (ginibreBrownianFullPastContinuousNoise n B α s ω).val t =
      ginibreConfigurationBrownianNoise n B α ω (min t (s : ℝ)) := by
  filter_upwards [ginibreBrownianFullPastRawPath_ae n B P hB α s,
    ginibreConfigurationBrownianNoise_actual n B P hB α] with ω hp h0
  intro t
  change ginibreBrownianFullPastRawPath n B α s ω t -
    ginibreBrownianFullPastRawPath n B α s ω 0 = _
  rw [hp t, hp 0]
  have hs0 : min (0 : ℝ) (s : ℝ) = 0 := min_eq_left s.property
  simp only [hs0, h0.2, sub_zero]

 theorem ginibreBrownianFullPastContinuousNoise_measurable {Ω : Type*} [mAmbient : MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (α : ℝ) (s : ℝ≥0) :
    @Measurable _ _ (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) s)
      (borel (GinibreContinuousNoise n)) (ginibreBrownianFullPastContinuousNoise n B α s) := by
  letI : MeasurableSpace C(ℝ, Configuration n) := borel _
  letI : BorelSpace C(ℝ, Configuration n) := ⟨rfl⟩
  exact (ginibreContinuousNoiseNormalize_continuous n).measurable.comp
    (ginibreBrownianFullPastRawPath_measurable n B P hB α s)

end
end GinibrePoincare
