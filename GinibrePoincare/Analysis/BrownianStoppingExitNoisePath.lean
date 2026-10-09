module

public import GinibrePoincare.Analysis.GinibreHamiltonianMaximalEvaluation
public import GinibrePoincare.Analysis.GinibreStochasticContinuousNoisePath

@[expose] public section

/-! The actual Brownian configuration noise as a full continuous zero-based path. -/
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 def ginibreContinuousNoiseNormalize (n : ℕ) (N : C(ℝ, Configuration n)) : GinibreContinuousNoise n :=
  ⟨N - ContinuousMap.const ℝ (N 0), by simp⟩

 theorem ginibreContinuousNoiseNormalize_continuous (n : ℕ) :
    Continuous (ginibreContinuousNoiseNormalize n) := by
  apply Continuous.subtype_mk
  exact continuous_id.sub (ContinuousMap.continuous_const'.comp (continuous_eval_const 0))

 def ginibreBrownianFullContinuousNoise {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ) (ω : Ω) : GinibreContinuousNoise n :=
  ginibreContinuousNoiseNormalize n
    (ContinuousMap.mkD (ginibreConfigurationBrownianNoise n B α ω) 0)

 theorem ginibreBrownianFullContinuousNoise_ae {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsBrownianReal (B i) P) (α : ℝ) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, (ginibreBrownianFullContinuousNoise n B α ω).val t =
      ginibreConfigurationBrownianNoise n B α ω t := by
  filter_upwards [ginibreConfigurationBrownianNoise_actual n B P hB α] with ω hω
  intro t
  simp [ginibreBrownianFullContinuousNoise, ginibreContinuousNoiseNormalize,
    ContinuousMap.mkD, hω.1, hω.2]

 theorem ginibreBrownianFullContinuousNoise_measurable {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (α : ℝ) :
    Measurable (ginibreBrownianFullContinuousNoise n B α) := by
  letI : MeasurableSpace C(ℝ, Configuration n) := borel _
  letI : BorelSpace C(ℝ, Configuration n) := ⟨rfl⟩
  apply (ginibreContinuousNoiseNormalize_continuous n).measurable.comp
  apply ginibre_measurable_continuousMap_of_evaluations
  intro t
  apply (aemeasurable_iff_measurable (μ := P)).mp
  have hNoise : Measurable (fun ω => ginibreConfigurationBrownianNoise n B α ω t) := by
    apply measurable_pi_lambda
    intro j
    exact (((aemeasurable_iff_measurable.mp ((hB (j, 0)).aemeasurable t.toNNReal)).complex_ofReal).add
      (measurable_const.mul ((aemeasurable_iff_measurable.mp
        ((hB (j, 1)).aemeasurable t.toNNReal)).complex_ofReal))).const_smul (Real.sqrt (2*α/(n : ℝ)^2))
  apply hNoise.aemeasurable.congr
  filter_upwards [ginibreConfigurationBrownianNoise_actual n B P hB α] with ω hω
  simp [ContinuousMap.mkD, hω.1]

end
end GinibrePoincare
