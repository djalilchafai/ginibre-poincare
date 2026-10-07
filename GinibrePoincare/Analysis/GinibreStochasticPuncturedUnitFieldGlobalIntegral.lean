module

public import GinibrePoincare.Analysis.GinibreStochasticPuncturedUnitFieldIntegral
public import GinibrePoincare.Analysis.GinibreStochasticUnitFieldGlobalIntegral

@[expose] public section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1500000

theorem ginibrePuncturedUnitField_global_continuous_integral_exists
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (u : ℝ≥0 → Ω → EuclideanSpace ℝ ι)
    (hu : ∀ t, @Measurable Ω (EuclideanSpace ℝ ι)
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) t) _ (u t))
    (hunit : ∀ t ω, ‖u t ω‖=1)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => u t ω) (Ioi 0)) (i₀ : ι) :
    ∃ J : ℝ≥0 → Ω → ℝ,
      Martingale J (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) P ∧
      (∀ᵐ ω ∂P, Continuous (fun t => J t ω)) ∧ (∀ t, MemLp (J t) 2 P) ∧
      J 0 =ᵐ[P] (fun _ => 0) ∧
      (∀ t, TendstoInMeasure P (fun k ω =>
        ∑ i, brownianUniformLeftSum (B i) (fun s ω => u s ω i) t (k+1) ω) atTop (J t)) ∧
      (∀ t, HasLaw (J t) (gaussianReal 0 t) P) := by
  classical
  have hex (n : ℕ) := ginibrePuncturedUnitField_continuous_integral_exists B P hB hind u hu hunit
    (n+1 : ℝ≥0) (by positivity) hc i₀
  choose M hM hMC hML hM0 hMS hMlaw using hex
  obtain ⟨J,hJM,hJC,hJL,hJ0,hJS⟩ := ginibreContinuousMartingale_global_of_horizon_limits P
    (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
    (fun t k ω => ∑ i, brownianUniformLeftSum (B i) (fun s ω => u s ω i) t (k+1) ω)
    M hM hMC hML hM0 hMS
  refine ⟨J,hJM,hJC,hJL,hJ0,hJS,?_⟩
  intro t
  exact brownianUnitField_integral_limit_gaussian B P (fun i => (hB i).toIsPreBrownianReal)
    hind u hu hunit i₀ t (J t) (hJS t)

#print axioms ginibrePuncturedUnitField_global_continuous_integral_exists
end
end GinibrePoincare
