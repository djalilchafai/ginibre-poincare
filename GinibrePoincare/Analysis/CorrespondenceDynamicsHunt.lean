module
public import GinibrePoincare.Analysis.CorrespondenceDynamicsStrongMarkov
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Continuity at arbitrary convergent times holds on one full-measure event;
in particular this proves the quasi-left-continuity required for a Hunt process. -/
theorem correspondence_ginibre_random_time_continuity
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    ∀ᵐ ω ∂P, ∀ (s : ℕ → ℝ≥0) (t : ℝ≥0), Tendsto s atTop (𝓝 t) →
      Tendsto (fun k => ginibreBrownianMaximalProcess n α z B (s k) ω) atTop
        (𝓝 (ginibreBrownianMaximalProcess n α z B t ω)) := by
  filter_upwards [(ginibreBrownianMaximalProcess_global_original_solution hn α z hz B P hB hind).2]
    with ω hω
  intro s t hs
  have hc := hω.1.comp NNReal.continuous_coe
  have ht := hc.continuousAt.tendsto.comp hs
  simpa only [Real.toNNReal_coe, Function.comp_def] using ht

/-- The original diffusion has continuous paths (hence right continuity and
quasi-left continuity), and the full strong Markov conditional law at every
finite stopping time in its completed Brownian filtration. -/
theorem correspondence_ginibre_continuous_strongMarkov
    {Ω A : Type*} [mAmbient : MeasurableSpace Ω] [MeasurableSpace A]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (z : {z : Configuration n // CollisionFree z})
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    (∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => ginibreBrownianMaximalProcess n α z.val B t ω)) ∧
    ∀ (τ : Ω → ℝ≥0)
      (hτ : IsStoppingTime (ginibreBrownianAugmentedFiltration B P
        (fun i => (hB i).toIsPreBrownianReal)) (fun ω => (τ ω : WithTop ℝ≥0)))
      (t : ℝ≥0) (Y : Ω → A) (hY : @Measurable Ω A hτ.measurableSpace _ Y),
      P.map (fun ω => (Y ω, ginibreBrownianStateProcess α z B (τ ω+t) ω)) =
        ((P.map (fun ω => (Y ω, ginibreBrownianStateProcess α z B (τ ω) ω))).prod
          (P.map (ginibreBrownianFullContinuousNoise n B α))).map
            (fun p => (p.1.1, ginibreCanonicalStateValue α t (p.1.2, p.2))) := by
  constructor
  · filter_upwards [(ginibreBrownianMaximalProcess_global_original_solution hn α z.val z.property B P hB hind).2]
      with ω hω
    simpa only [Real.toNNReal_coe, Function.comp_def] using hω.1.comp NNReal.continuous_coe
  · exact fun τ hτ t Y hY => correspondence_ginibre_stopping_future_past_joint_law
      hn α z B P hB hind τ hτ t Y hY

#print axioms correspondence_ginibre_random_time_continuity
#print axioms correspondence_ginibre_continuous_strongMarkov
end
end GinibrePoincare
