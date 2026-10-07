module

public import GinibrePoincare.Analysis.GinibreHamiltonianOUInteractionIto
public import GinibrePoincare.Analysis.GinibreHamiltonianInteractionTilt
public import GinibrePoincare.Analysis.GinibreHamiltonianOUActionExpansion

@[expose] public section

/-! The actual normalized Brownian interaction likelihood equals the literal
OU-relative Hamiltonian action through a genuine positive stopping time. -/
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem ginibreHamiltonianOU_interaction_action_density_exists {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z) :
    ∃ T : ℝ≥0, 0 < T ∧ ∃ K : Set (Configuration n), IsCompact K ∧
      (∀ x ∈ K, CollisionFree x) ∧ ∃ Y : ℝ≥0 → Ω → Configuration n,
      (∀ ω, Continuous (fun t => Y t ω)) ∧ (∀ t ω, Y t ω ∈ K) ∧
      (∀ ω, Y 0 ω = z) ∧
      StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) Y ∧
      ∃ θ : Ω → ℝ≥0,
      IsStoppingTime (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
        (fun ω => (θ ω : WithTop ℝ≥0)) ∧ (∀ ω, 0 < θ ω ∧ θ ω ≤ T) ∧
      (∀ᵐ ω ∂P, ∀ t ≤ θ ω, Y t ω = z+ginibreConfigurationBrownianNoise n B α ω t+
        ∫ s in (0 : ℝ)..t, (-2*(α : ℝ)/(n : ℝ)) • Y s.toNNReal ω) ∧
      ∃ M : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ,
      (∀ i, Martingale (M i) (ginibreBrownianAugmentedFiltration B P
        (fun i => (hB i).toIsPreBrownianReal)) P ∧
        (∀ ω, Continuous (fun t => M i t ω)) ∧ (∀ t, MemLp (M i t) 2 P) ∧
        M i 0 =ᵐ[P] (fun _ => 0) ∧
        ∀ t ≤ T, TendstoInMeasure P
          (fun k => brownianUniformLeftSum (B i)
            (fun r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) t (k+1)) atTop (M i t)) ∧
      Integrable (brownianVectorExponentialIntegralDensity
        (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) T (fun i => M i T)) P ∧
      (∫ ω, brownianVectorExponentialIntegralDensity
        (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) T (fun i => M i T) ω ∂P)=1 ∧
      ∀ᵐ ω ∂P, ∀ t ≤ θ ω,
        brownianVectorExponentialIntegralDensity
          (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) t (fun i => M i t) ω =
        Real.exp (ginibreInteractionPotential n z) *
          (ginibreHamiltonianGradientPathWeight n α (t : ℝ) (fun s => Y s.toNNReal ω) /
            ginibreQuadraticGradientPathWeight n α (t : ℝ) (fun s => Y s.toNNReal ω)) := by
  obtain ⟨T,hT,K,hK,hCF,Y,hYC,hYR,hY0,hY,θ,hStop,hθ,hEq,J,hJM,hJC,hJL,hJ0,hLimit,hIto⟩ :=
    ginibreHamiltonianOU_interaction_ito_exists n B P hB hind α z hz
  obtain ⟨M,hM,hDi,hD1⟩ := ginibreInteractionBrownianTilt_exponential_exists
    n B P hB hind α Y hY hYC K hK hCF hYR T
  have hSum := ginibreInteractionBrownianTilt_integrals_eq_gradient n B P hB hind α Y hY
    K hK hCF hYR T J hJC hLimit M (fun i => (hM i).2.1) (fun i => (hM i).2.2.2.2)
  refine ⟨T,hT,K,hK,hCF,Y,hYC,hYR,hY0,hY,θ,hStop,hθ,hEq,M,hM,hDi,hD1,?_⟩
  filter_upwards [hSum,hIto] with ω hSumω hItoω
  intro t ht
  have hMt := hSumω t (ht.trans (hθ ω).2)
  have hIt := hItoω t ht
  have hEnergy : brownianVectorTimeEnergy
      (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) t ω =
      (α/(2*(n : ℝ)^2)) * ∫ s in (0 : ℝ)..t, ginibreInteractionGradientNormSq n (Y s.toNNReal ω) := by
    unfold brownianVectorTimeEnergy
    simp_rw [ginibreInteractionBrownianTilt_energy n α α.property]
    rw [intervalIntegral.integral_const_mul]
  have hx : ContinuousOn (fun s : ℝ => Y s.toNNReal ω) (Icc 0 (t : ℝ)) :=
    ((hYC ω).comp continuous_real_toNNReal).continuousOn
  have hex := ginibreHamiltonianOUPathQuotient_expansion hn α (t : ℝ) t.property
    (fun s : ℝ => Y s.toNNReal ω) hx (fun s hs => hCF _ (hYR _ _))
  rw [hex]
  unfold brownianVectorExponentialIntegralDensity
  rw [hMt,hEnergy,← Real.exp_add]
  rw [Real.toNNReal_zero,hY0,Real.toNNReal_coe]
  apply congrArg Real.exp
  rw [← hIt]
  ring

#print axioms ginibreHamiltonianOU_interaction_action_density_exists
end
end GinibrePoincare
