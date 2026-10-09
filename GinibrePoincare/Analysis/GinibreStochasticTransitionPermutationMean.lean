module

public import GinibrePoincare.Analysis.GinibreStochasticTransitionPermutationNoise
public import GinibrePoincare.Analysis.GinibreStochasticTransitionContinuousMean

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem ginibreStationaryContinuousTransitionMean_permute {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (σ : ParticlePermutation n) (α : ℝ≥0)
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P)
    (v : Configuration n → ℝ) (hv : Measurable v) (T : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z) :
    ginibreStationaryContinuousTransitionMean α B P (fun y => v (permute σ y)) (T : ℝ) z=
      ginibreStationaryContinuousTransitionMean α B P v (T : ℝ) (permute σ z) := by
  rw [ginibreStationaryContinuousTransitionMean_eq_original hn α P B hB hiB _ z hz,
    ginibreStationaryContinuousTransitionMean_eq_original hn α P B hB hiB v (permute σ z)
      (ginibreCollisionFree_permute σ hz), Real.toNNReal_coe]
  let F := fun N : GinibreContinuousNoise n =>
    v (ginibreDrivenMaximalValue n α N.val (permute σ z) T)
  have hF : Measurable F := hv.comp (ginibreDrivenMaximalValue_measurable hn α (permute σ z) T)
  have hN := ginibreBrownianFullContinuousNoise_measurable n B P hB α
  have hPN : Measurable (fun ω => ginibreContinuousNoisePermute σ (ginibreBrownianFullContinuousNoise n B α ω)) :=
    (ginibreContinuousNoisePermute_continuous σ).measurable.comp hN
  have he := congrArg (fun ν : Measure (GinibreContinuousNoise n) => ∫ N, F N ∂ν)
    (ginibreBrownian_continuous_noise_permute_law σ B P hB hiB α)
  rw [integral_map hPN.aemeasurable hF.aestronglyMeasurable,
    integral_map hN.aemeasurable hF.aestronglyMeasurable] at he
  refine (integral_congr_ae (ae_of_all P ?_)).trans he
  intro ω
  change v (permute σ (ginibreDrivenMaximalValue n α _ z T))=
    v (ginibreDrivenMaximalValue n α _ (permute σ z) T)
  congr 1
  have hNoise : ((ginibreContinuousNoisePermute σ (ginibreBrownianFullContinuousNoise n B α ω)).val :
      ℝ → Configuration n)=fun s => permute σ ((ginibreBrownianFullContinuousNoise n B α ω).val s) := by
    funext s
    exact ginibreParticlePermutationCLM_apply σ _
  rw [hNoise, ginibreDrivenMaximalValue_permute]

#print axioms ginibreStationaryContinuousTransitionMean_permute
end
end GinibrePoincare
