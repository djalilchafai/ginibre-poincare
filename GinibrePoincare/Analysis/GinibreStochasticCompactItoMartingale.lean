module

public import GinibrePoincare.Analysis.GinibreStochasticGradientIntegralAllHorizons
public import GinibrePoincare.Analysis.GinibreStochasticItoUntilStopping

@[expose] public section

/-! Actual local Itô identities hold simultaneously through an actual bounded stopping time. -/
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1500000

theorem ginibreCompactVolterra_continuous_ito_martingale_exists
    {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0)
    (X : ℝ≥0 → Ω → Configuration n)
    (hX : StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) X)
    (hCont : ∀ ω, Continuous (fun t => X t ω))
    (f : Configuration n → ℝ) (U K : Set (Configuration n))
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hRange : ∀ t ω, X t ω ∈ K) (T : ℝ≥0)
    (b : ℝ → Ω → Configuration n) (hb : ∀ ω, Continuous (fun s => b s ω))
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ s ∈ Icc (0 : ℝ) T, ∀ ω, ‖b s ω‖ ≤ M)
    (θ : Ω → ℝ≥0) (hθ : Measurable θ) (hθT : ∀ ω, θ ω ≤ T)
    (hVolterra : ∀ᵐ ω ∂P, ∀ t ≤ θ ω, X t ω=X 0 ω+
      (ginibreConfigurationBrownianNoise n B α ω t-ginibreConfigurationBrownianNoise n B α ω 0)+
      ∫ s in (0 : ℝ)..(t : ℝ), b s ω)
 :
    ∃ J : ℝ≥0 → Ω → ℝ,
      Martingale J (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) P ∧
      (∀ ω, Continuous (fun t => J t ω)) ∧ (∀ t, MemLp (J t) 2 P) ∧ J 0 =ᵐ[P] (fun _ => 0) ∧
      ∀ᵐ ω ∂P, ∀ t ≤ θ ω, ginibreConfigurationTestCompensator n α X f b t ω=J t ω := by
  obtain ⟨J,hJM,hJC,hJL,hJ0,hPartial,hLimit⟩ := ginibreCompactProcess_continuous_gradient_integral_all_horizons
    n B P hB hind α X hX hCont f U K hU hf hK hKU hRange T
  refine ⟨J,hJM,hJC,hJL,hJ0,?_⟩
  exact ginibreCompactVolterra_compensator_eq_gradient_process_until n B P hB hind α X hX hCont
    f U K hU hf hK hKU hRange T b hb M hM hbound θ hθ hθT hVolterra
    J (Filter.Eventually.of_forall hJC) hLimit
end
end GinibrePoincare
