module

public import GinibrePoincare.Analysis.GinibreStochasticCausalFlowAdaptation

@[expose] public section

/-! Actual measurable local solution selection for all configuration Brownian coordinates. -/
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem ginibreBrownian_adapted_local_solution_selection {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (α : ℝ) (z : Configuration n) (hz : CollisionFree z) :
    ∃ τ : ℝ, ∃ hτ : τ > 0, ∃ X : Ω → C(Icc 0 τ, Configuration n),
      @Measurable _ _ _ (borel C(Icc 0 τ, Configuration n)) X ∧
      (∀ ω, X ω ⟨0, ⟨le_rfl, hτ.le⟩⟩ = z) ∧
      (∀ ω t, CollisionFree (X ω t)) ∧
      StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
        (fun s ω => X ω (Set.projIcc 0 τ hτ.le (s : ℝ))) ∧
      ∀ᵐ ω ∂P, ∃ θ > (0 : ℝ), θ ≤ τ ∧ ∀ t : Icc 0 τ, (t : ℝ) ≤ θ →
        X ω t = z+ginibreConfigurationBrownianNoise n B α ω t+
          ∫ s in (0 : ℝ)..t, ginibreLangevinDrift n α (X ω (Set.projIcc 0 τ hτ.le s)) := by
  obtain ⟨δ, hδ, τ, hτ, Φ, hMeas, hZero, hCF, hEq, hCausal⟩ :=
    ginibreDrivenPath_clipped_measurable_local_flow n α z hz
  let X := fun ω => Φ (ginibreConfigurationBrownianContinuousPath n B α ω)
  refine ⟨τ, hτ, X, hMeas.comp (ginibreConfigurationBrownianContinuousPath_measurable n B P hB α),
    fun ω => hZero _, fun ω t => hCF _ t,
    ginibreBrownian_causal_flow_stronglyAdapted n B P hB α τ hτ Φ hMeas hCausal,?_⟩
  filter_upwards [ginibreConfigurationBrownianContinuousPath_ae n B P hB α,
    ginibreConfigurationBrownianNoise_actual n B P hB α] with ω hPath hNoise
  have hr := drivenNoiseClipRadius_pos δ hδ
  obtain ⟨η, hη, hSmall⟩ := Metric.continuousAt_iff.mp (hNoise.1.continuousAt (x := (0 : ℝ))) _ hr
  let θ := min τ (min 1 (η/2))
  have hθ : 0 < θ := lt_min hτ (lt_min (by norm_num) (by positivity))
  refine ⟨θ, hθ, min_le_left _ _,?_⟩
  intro t ht
  have ht1 : (t : ℝ) ≤ 1 := ht.trans ((min_le_right τ _).trans (min_le_left _ _))
  have htη : (t : ℝ) < η := lt_of_le_of_lt
    (ht.trans ((min_le_right τ _).trans (min_le_right _ _))) (by linarith)
  have hNorm : ‖ginibreConfigurationBrownianNoise n B α ω t‖ ≤ drivenNoiseClipRadius δ := by
    have h := hSmall (x := (t : ℝ)) (by simpa [dist_eq_norm, Real.norm_of_nonneg t.property.1] using htη)
    rw [hNoise.2, dist_zero_right] at h
    exact h.le
  have hClip : drivenBoundedNoiseExtension (Configuration n)
      (drivenNoiseClipSmall δ hδ (ginibreConfigurationBrownianContinuousPath n B α ω)).val t =
      ginibreConfigurationBrownianNoise n B α ω t := by
    have htm : (t : ℝ) ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [t.property.1], ht1⟩
    change drivenNoiseClip (drivenNoiseClipRadius δ)
      (ginibreConfigurationBrownianContinuousPath n B α ω (Set.projIcc (-1 : ℝ) 1 (by norm_num) t)-
        ginibreConfigurationBrownianContinuousPath n B α ω ⟨0, by norm_num⟩) = _
    rw [Set.projIcc_of_mem (by norm_num) htm, hPath ⟨t, htm⟩, hPath ⟨0, by norm_num⟩, hNoise.2, sub_zero]
    exact drivenNoiseClip_eq _ hr _ hNorm
  exact (hEq (ginibreConfigurationBrownianContinuousPath n B α ω) t).trans (by rw [hClip])

end
end GinibrePoincare
