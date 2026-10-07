module

public import GinibrePoincare.Analysis.GinibreStochasticTransitionPermutationMaximal
public import GinibrePoincare.Analysis.BrownianOrthogonalContinuousPathLaw

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem ginibreBrownian_continuous_noise_family_law_eq {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B C : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hC : ∀ i, IsBrownianReal (C i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (hindC : iIndepFun (fun i ω t => C i t ω) P) (α : ℝ) :
    P.map (ginibreBrownianFullContinuousNoise n C α) =
      P.map (ginibreBrownianFullContinuousNoise n B α) := by
  letI : MeasurableSpace C(ℝ,Configuration n) := borel _
  letI : BorelSpace C(ℝ,Configuration n) := ⟨rfl⟩
  let X := ginibreBrownianFullContinuousNoise n C α
  let Y := ginibreBrownianFullContinuousNoise n B α
  have hshift := hC
  have hX : Measurable X := ginibreBrownianFullContinuousNoise_measurable n _ P hshift α
  have hY : Measurable Y := ginibreBrownianFullContinuousNoise_measurable n _ P hB α
  have hXm : Measurable (fun ω i t => C i t ω) := by
    apply measurable_pi_lambda
    intro i
    exact brownianScalar_whole_path_measurable P _ (hshift i).toIsPreBrownianReal
  have hYm : Measurable (fun ω i t => B i t ω) := by
    apply measurable_pi_lambda
    intro i
    exact brownianScalar_whole_path_measurable P _ (hB i).toIsPreBrownianReal
  have hraw : P.map (fun ω => ginibreConfigurationBrownianNoise n C α ω) =
      P.map (fun ω => ginibreConfigurationBrownianNoise n B α ω) := by
    have hh := congrArg (Measure.map (brownianConfigurationNoisePathMap n α))
      (brownianFamily_whole_path_law_eq P C B (fun i => (hC i).toIsPreBrownianReal)
        (fun i => (hB i).toIsPreBrownianReal) hindC hind)
    rw [Measure.map_map (brownianConfigurationNoisePathMap_measurable n α) hXm,
      Measure.map_map (brownianConfigurationNoisePathMap_measurable n α) hYm] at hh
    exact hh
  have hXL : (fun ω => ginibreConfigurationBrownianNoise n C α ω) =ᵐ[P]
      (fun ω t => (X ω).val t) :=
    (ginibreBrownianFullContinuousNoise_ae n _ P hshift α).mono fun ω hω => (funext hω).symm
  have hYL : (fun ω => ginibreConfigurationBrownianNoise n B α ω) =ᵐ[P]
      (fun ω t => (Y ω).val t) :=
    (ginibreBrownianFullContinuousNoise_ae n _ P hB α).mono fun ω hω => (funext hω).symm
  have hval : Continuous (fun f : GinibreContinuousNoise n => f.val) := continuous_subtype_val
  have hCM : P.map (fun ω => (X ω).val) = P.map (fun ω => (Y ω).val) := by
    apply continuousMap_law_eq_of_whole_path_law_eq P (fun ω => (X ω).val) (fun ω => (Y ω).val)
      (hval.measurable.comp hX) (hval.measurable.comp hY)
    exact (Measure.map_congr hXL).symm.trans (hraw.trans (Measure.map_congr hYL))
  have hclosed : IsClosed {f : C(ℝ,Configuration n) | f 0 = 0} :=
    isClosed_eq (continuous_eval_const 0) continuous_const
  have hec : Topology.IsClosedEmbedding (fun f : GinibreContinuousNoise n => f.val) :=
    hclosed.isClosedEmbedding_subtypeVal
  apply hec.measurableEmbedding.map_injective
  rw [Measure.map_map hec.measurableEmbedding.measurable hX,
    Measure.map_map hec.measurableEmbedding.measurable hY]
  exact hCM

def ginibreParticleBrownianRelabel {Ω : Type*} {n : ℕ} (σ : ParticlePermutation n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ :=
  fun i => B (σ i.1,i.2)

def ginibreContinuousNoisePermute {n : ℕ} (σ : ParticlePermutation n)
    (N : GinibreContinuousNoise n) : GinibreContinuousNoise n :=
  ⟨(⟨ginibreParticlePermutationCLM σ,(ginibreParticlePermutationCLM σ).continuous⟩ :
    C(Configuration n,Configuration n)).comp N.val, by
      change ginibreParticlePermutationCLM σ (N.val 0)=0
      rw [N.property,map_zero]⟩

theorem ginibreContinuousNoisePermute_continuous {n : ℕ} (σ : ParticlePermutation n) :
    Continuous (ginibreContinuousNoisePermute σ) := by
  apply Continuous.subtype_mk
  exact ((⟨ginibreParticlePermutationCLM σ,(ginibreParticlePermutationCLM σ).continuous⟩ :
    C(Configuration n,Configuration n)).continuous_postcomp).comp continuous_subtype_val

theorem ginibreBrownian_relabel_independent {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (σ : ParticlePermutation n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hi : iIndepFun (fun i ω t => B i t ω) P) :
    iIndepFun (fun i ω t => ginibreParticleBrownianRelabel σ B i t ω) P := by
  exact hi.precomp (Equiv.prodCongr σ (Equiv.refl (Fin 2))).injective

theorem ginibreBrownian_relabel_continuous_noise_ae {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (σ : ParticlePermutation n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) (hB : ∀ i, IsBrownianReal (B i) P) (α : ℝ) :
    ginibreBrownianFullContinuousNoise n (ginibreParticleBrownianRelabel σ B) α =ᵐ[P]
      (fun ω => ginibreContinuousNoisePermute σ (ginibreBrownianFullContinuousNoise n B α ω)) := by
  have hC : ∀ i, IsBrownianReal (ginibreParticleBrownianRelabel σ B i) P := fun i => hB (σ i.1,i.2)
  filter_upwards [ginibreBrownianFullContinuousNoise_ae n B P hB α,
    ginibreBrownianFullContinuousNoise_ae n _ P hC α] with ω hω hω'
  apply Subtype.ext
  ext t j
  change (ginibreBrownianFullContinuousNoise n _ α ω).val t j=
    (ginibreParticlePermutationCLM σ ((ginibreBrownianFullContinuousNoise n B α ω).val t)) j
  rw [ginibreParticlePermutationCLM_apply,hω,hω']
  rfl

theorem ginibreBrownian_continuous_noise_permute_law {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (σ : ParticlePermutation n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hi : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ) :
    P.map (fun ω => ginibreContinuousNoisePermute σ (ginibreBrownianFullContinuousNoise n B α ω))=
      P.map (ginibreBrownianFullContinuousNoise n B α) := by
  rw [← Measure.map_congr (ginibreBrownian_relabel_continuous_noise_ae σ B P hB α)]
  exact ginibreBrownian_continuous_noise_family_law_eq n B (ginibreParticleBrownianRelabel σ B) P hB
    (fun i => hB (σ i.1,i.2)) hi (ginibreBrownian_relabel_independent σ B P hi) α

#print axioms ginibreBrownian_continuous_noise_permute_law
#print axioms ginibreBrownian_continuous_noise_family_law_eq
end
end GinibrePoincare
