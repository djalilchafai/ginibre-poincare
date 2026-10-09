module

public import GinibrePoincare.Analysis.GinibreDrivenPathClippedLocalFlow
public import GinibrePoincare.Analysis.GinibreStochasticContinuousPastPath

@[expose] public section

/-! Causal actual Brownian path selections are adapted to the genuine augmented past. -/
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem ginibreBrownian_causal_flow_stronglyAdapted {Ω : Type*} [mAmbient : MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (α τ : ℝ) (hτ : 0 < τ)
    (Φ : C(Icc (-1 : ℝ) 1, Configuration n) → C(Icc 0 τ, Configuration n))
    (hMeas : @Measurable _ _ (borel C(Icc (-1 : ℝ) 1, Configuration n))
      (borel C(Icc 0 τ, Configuration n)) Φ)
    (hCausal : ∀ N Q (t : Icc 0 τ),
      (∀ u ∈ Icc 0 (t : ℝ), N (Set.projIcc (-1 : ℝ) 1 (by norm_num) u) =
        Q (Set.projIcc (-1 : ℝ) 1 (by norm_num) u)) → Φ N t = Φ Q t) :
    StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
      (fun s ω => Φ (ginibreConfigurationBrownianContinuousPath n B α ω) (Set.projIcc 0 τ hτ.le (s : ℝ))) := by
  intro s
  let t := Set.projIcc 0 τ hτ.le (s : ℝ)
  have hts : (t : ℝ) ≤ (s : ℝ) := by
    rw [show (t : ℝ) = max 0 (min τ (s : ℝ)) from rfl]
    exact max_le s.coe_nonneg (min_le_right _ _)
  have hPastMeas := ginibreConfigurationBrownianPastContinuousPath_measurable n B P hB α s
  have hAE₁ := ginibreConfigurationBrownianContinuousPath_ae n B P hB α
  have hAE₂ := ginibreConfigurationBrownianPastContinuousPath_ae n B P hB α s
  have hm := ginibreBrownianFamilyPastSpace_le B P (fun i => (hB i).toIsPreBrownianReal) s
  let mPast := ginibreBrownianFamilyPastSpace B s
  let mAug := ginibreNullAugmentation (mAmbient := mAmbient) P mPast
  have hAug := ginibreNullAugmentation_le (mAmbient := mAmbient) P mPast hm
  let μ := P.trim hAug
  haveI : μ.IsComplete := ginibreNullAugmentation_trim_complete (mAmbient := mAmbient) P mPast hm
  letI : MeasurableSpace C(Icc 0 τ, Configuration n) := borel _
  letI : BorelSpace C(Icc 0 τ, Configuration n) := ⟨rfl⟩
  have hEval : @Measurable C(Icc 0 τ, Configuration n) (Configuration n) (borel _) _ (fun f => f t) :=
    (continuous_eval_const t).measurable
  have hSelectedPast : @Measurable Ω (Configuration n) mAug _
      (fun ω => Φ (ginibreConfigurationBrownianPastContinuousPath n B α s ω) t) :=
    hEval.comp (hMeas.comp hPastMeas)
  have hEqual : (fun ω => Φ (ginibreConfigurationBrownianPastContinuousPath n B α s ω) t) =ᵐ[μ]
      (fun ω => Φ (ginibreConfigurationBrownianContinuousPath n B α ω) t) := by
    have hAE := ginibreNullAugmentation_ae_transfer (mAmbient := mAmbient) P mPast hm _ (hAE₁.and hAE₂)
    filter_upwards [hAE] with ω hω
    apply hCausal
    intro u hu
    rw [hω.2 _, hω.1 _]
    have hcu : ((Set.projIcc (-1 : ℝ) 1 (by norm_num) u) : ℝ) ≤ (s : ℝ) := by
      rw [Set.coe_projIcc]
      exact (max_le (by linarith [hu.1]) (min_le_right _ _)).trans (hu.2.trans hts)
    rw [min_eq_left hcu]
  exact ((aemeasurable_iff_measurable (μ := μ)).mp (hSelectedPast.aemeasurable.congr hEqual)).stronglyMeasurable

end
end GinibrePoincare
