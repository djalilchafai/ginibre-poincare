module

public import GinibrePoincare.Analysis.GinibreStochasticCausalFlowAdaptation
public import GinibrePoincare.Analysis.GinibreStochasticContinuousStoppingTime

@[expose] public section

/-! An everywhere continuous, genuinely adapted realization of actual configuration noise up to time one. -/
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def ginibreConfigurationNoiseRestriction (n : ℕ)
    (N : C(Icc (-1 : ℝ) 1,Configuration n)) : C(Icc (0 : ℝ) 1,Configuration n) :=
  ⟨fun t => N ⟨t,⟨by linarith [t.property.1],t.property.2⟩⟩-N ⟨0,by norm_num⟩,
    (N.continuous.comp (continuous_subtype_val.subtype_mk _)).sub continuous_const⟩

theorem ginibreConfigurationNoiseRestriction_continuous (n : ℕ) : Continuous (ginibreConfigurationNoiseRestriction n) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_eval.comp (continuous_fst.prodMk
    ((continuous_subtype_val.comp continuous_snd).subtype_mk _))).sub
      ((continuous_eval_const _).comp continuous_fst)

def ginibreConfigurationContinuousNoise {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ) (t : ℝ≥0) (ω : Ω) : Configuration n :=
  ginibreConfigurationNoiseRestriction n (ginibreConfigurationBrownianContinuousPath n B α ω)
    (Set.projIcc 0 1 (by norm_num) (t : ℝ))

theorem ginibreConfigurationContinuousNoise_continuous {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ) (ω : Ω) :
    Continuous (fun t => ginibreConfigurationContinuousNoise n B α t ω) :=
  (ginibreConfigurationNoiseRestriction n _).continuous.comp (continuous_projIcc.comp NNReal.continuous_coe)

theorem ginibreConfigurationContinuousNoise_zero {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ) (ω : Ω) :
    ginibreConfigurationContinuousNoise n B α 0 ω = 0 := by
  simp [ginibreConfigurationContinuousNoise,ginibreConfigurationNoiseRestriction,Set.projIcc_left]

theorem ginibreConfigurationContinuousNoise_stronglyAdapted {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (α : ℝ) :
    StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
      (ginibreConfigurationContinuousNoise n B α) := by
  apply ginibreBrownian_causal_flow_stronglyAdapted n B P hB α 1 (by norm_num)
    (ginibreConfigurationNoiseRestriction n) (ginibreConfigurationNoiseRestriction_continuous n).borel_measurable
  intro N Q t hPast
  have h0 := hPast 0 ⟨le_rfl,t.property.1⟩
  have ht := hPast t ⟨t.property.1,le_rfl⟩
  have htm : (t : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [t.property.1],t.property.2⟩
  simp only [Set.projIcc_of_mem (by norm_num : (-1 : ℝ) ≤ 1) htm] at ht
  simp only [Set.projIcc_of_mem (by norm_num : (-1 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ∈ Icc (-1 : ℝ) 1)] at h0
  exact congrArg₂ (fun x y : Configuration n => x-y) ht h0

theorem ginibreConfigurationContinuousNoise_actual_ae {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsBrownianReal (B i) P) (α : ℝ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ 1 → ginibreConfigurationContinuousNoise n B α t ω =
      ginibreConfigurationBrownianNoise n B α ω (t : ℝ) := by
  filter_upwards [ginibreConfigurationBrownianContinuousPath_ae n B P hB α,
    ginibreConfigurationBrownianNoise_actual n B P hB α] with ω hPath hNoise
  intro t ht
  have htm : (t : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨t.coe_nonneg,by exact_mod_cast ht⟩
  simp only [ginibreConfigurationContinuousNoise,Set.projIcc_of_mem (by norm_num) htm]
  change ginibreConfigurationBrownianContinuousPath n B α ω _-
    ginibreConfigurationBrownianContinuousPath n B α ω _ = _
  rw [hPath _,hPath _,hNoise.2,sub_zero]

end
end GinibrePoincare
