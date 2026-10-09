module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralExponentialLimit

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem itoUniformNNTime_eq_ginibreUniformBrownianTime (T : ℝ≥0) (n k : ℕ) :
    itoUniformNNTime T (n+1) k = ginibreUniformBrownianTime T n k := by
  apply NNReal.coe_injective
  rw [itoUniformNNTime_coe, ginibreUniformBrownianTime_coe]
  simp only [itoUniformTime, ginibreUniformTime, Nat.cast_add, Nat.cast_one]

/-- The finite Gaussian change-of-measure density is literally the exponential
 of the actual Brownian left sums minus half the actual energy Riemann sum. -/
theorem brownianPredictableVectorGaussianDensity_uniform_eq {Ω ι : Type*} [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (F : ι → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) :
    brownianPredictableVectorGaussianDensity B
      (fun k ω i => F i (itoUniformNNTime T (n+1) k) ω)
      (itoUniformNNTime T (n+1)) (n+1) = brownianVectorExponentialUniformSum B F T n := by
  classical
  funext ω
  unfold brownianPredictableVectorGaussianDensity brownianVectorExponentialUniformSum
    brownianVectorTimeEnergyUniformSum brownianUniformLeftSum
  apply congrArg Real.exp
  simp_rw [Finset.sum_sub_distrib, Finset.sum_div, itoUniformNNTime_increment_sub_coe]
  rw [Finset.sum_comm]
  congr 1
  simp_rw [← Finset.sum_div,← Finset.sum_mul]
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => ∑ i, (F i (ginibreUniformBrownianTime T n k) ω)^2) (n+1)]
  simp only [itoUniformNNTime_eq_ginibreUniformBrownianTime, Nat.cast_add, Nat.cast_one]

/-- For the genuine coordinate integral limits, the actual exponential density
 has expectation one; uniform integrability and L¹ convergence are derived. -/
theorem brownianVectorExponentialIntegralDensity_normalized {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (F : ι → ℝ≥0 → Ω → ℝ)
    (hF : ∀ i t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F i t))
    (C : ℝ) (hC : 0≤C) (hb : ∀ t ω, (∑ i, (F i t ω)^2)≤C^2)
    (T : ℝ≥0)
    (hc : ∀ i, ∀ᵐ ω ∂P, ContinuousOn (fun s => F i s ω) (Set.Icc 0 T))
    (hs : ∀ i n, AEStronglyMeasurable (brownianUniformLeftSum (B i) (F i) T (n+1)) P)
    (I : ι → Ω → ℝ)
    (hI : ∀ i, TendstoInMeasure P
      (fun n => brownianUniformLeftSum (B i) (F i) T (n+1)) atTop (I i)) :
    Integrable (brownianVectorExponentialIntegralDensity F T I) P ∧
      (0≤ᵐ[P] brownianVectorExponentialIntegralDensity F T I) ∧
      (∫ ω, brownianVectorExponentialIntegralDensity F T I ω ∂P)=1 ∧
      Tendsto (fun n => eLpNorm (brownianVectorExponentialUniformSum B F T n-
        brownianVectorExponentialIntegralDensity F T I) 1 P) atTop (𝓝 0) := by
  have hh : ∀ t, @Measurable Ω (ι→ℝ) (ginibreBrownianAugmentedFiltration B P hB t) _
      (fun ω i => F i t ω) := by
    intro t
    letI : MeasurableSpace Ω := ginibreBrownianAugmentedFiltration B P hB t
    apply measurable_pi_lambda
    intro i
    exact hF i t
  have hm : ∀ i t, Measurable (F i t) := fun i t =>
    (hF i t).mono ((ginibreBrownianAugmentedFiltration B P hB).le t) le_rfl
  have hl := brownianVectorExponentialUniformSum_tendstoInMeasure P B F T hm hc hs I hI
  have he := brownianPredictableVectorGaussianDensity_uniform_limit_normalized B P hB hind
    (fun t ω i => F i t ω) hh C hC hb T (brownianVectorExponentialIntegralDensity F T I) (by
      simpa only [brownianPredictableVectorGaussianDensity_uniform_eq] using hl)
  simpa only [brownianPredictableVectorGaussianDensity_uniform_eq] using he

end
end GinibrePoincare
