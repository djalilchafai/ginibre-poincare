module
public import GinibrePoincare.Analysis.CorrespondenceDynamicsBrownianStrongMarkov
@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem correspondenceBrownian_stopped_noise_independent
    {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (α : ℝ) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal)) (fun ω => (τ ω : WithTop ℝ≥0)))
    (Y : Ω → A) (hY : @Measurable Ω A hτ.measurableSpace _ Y) :
    let N := fun ω => correspondenceNoiseShift n (τ ω) (ginibreBrownianFullContinuousNoise n B α ω)
    Measurable N ∧ P.map N = P.map (ginibreBrownianFullContinuousNoise n B α) ∧
      IndepFun N Y P := by
  let N := fun ω => correspondenceNoiseShift n (τ ω) (ginibreBrownianFullContinuousNoise n B α ω)
  have htm : Measurable τ := by
    convert hτ.measurable'.untopD 0 using 1
    rfl
  have hN : Measurable N := (correspondenceNoiseShift_continuous n).measurable.comp
    (htm.prodMk (ginibreBrownianFullContinuousNoise_measurable n B P hB α))
  have hLaw : P.map N = P.map (ginibreBrownianFullContinuousNoise n B α) := by
    simpa only [Measure.restrict_univ,measure_univ,one_smul] using
      correspondenceBrownian_stopping_fresh_noise n B P hB hind α τ hτ univ MeasurableSet.univ
  refine ⟨hN,hLaw,?_⟩
  apply (indepFun_iff_measure_inter_preimage_eq_mul).mpr
  intro C D hC hD
  have hh := correspondenceBrownian_stopping_fresh_noise n B P hB hind α τ hτ (Y ⁻¹' D) (hY hD)
  have hh' := congrArg (fun μ : Measure (GinibreContinuousNoise n) => μ C) hh
  rw [Measure.map_apply hN hC,Measure.restrict_apply (hN hC),Measure.smul_apply,
    ← hLaw,Measure.map_apply hN hC] at hh'
  simpa only [N,smul_eq_mul,mul_comm] using hh'

#print axioms correspondenceBrownian_stopped_noise_independent
end
end GinibrePoincare
