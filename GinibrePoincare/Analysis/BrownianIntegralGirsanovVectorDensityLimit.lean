module

public import GinibrePoincare.Analysis.BrownianIntegralGirsanovVectorFiniteMoments
public import GinibrePoincare.Analysis.BrownianIntegralGirsanovDensityLimit
public import GinibrePoincare.Analysis.FiniteDimensionalItoUniformRefinement

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000

/-- Normalization and L¹ convergence of the actual vector Girsanov density
from genuine original-family finite Gaussian laws and derived uniform
integrability. The probability limit may be supplied by actual stochastic
integral and Riemann-sum convergence. -/
theorem brownianPredictableVectorGaussianDensity_uniform_limit_normalized
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (h : ℝ≥0 → Ω → ι → ℝ)
    (hh : ∀ r, @Measurable Ω (ι→ℝ) (ginibreBrownianAugmentedFiltration B P hB r) _ (h r))
    (C : ℝ) (hC : 0≤C) (hb : ∀ r ω, (∑ i, (h r ω i)^2)≤C^2)
    (T : ℝ≥0) (D : Ω → ℝ)
    (hlim : TendstoInMeasure P (fun n => brownianPredictableVectorGaussianDensity B
      (fun k => h (itoUniformNNTime T (n+1) k)) (itoUniformNNTime T (n+1)) (n+1)) atTop D) :
    Integrable D P ∧ (0≤ᵐ[P] D) ∧ (∫ ω, D ω ∂P)=1 ∧
      Tendsto (fun n => eLpNorm
        (brownianPredictableVectorGaussianDensity B (fun k => h (itoUniformNNTime T (n+1) k))
          (itoUniformNNTime T (n+1)) (n+1)-D) 1 P) atTop (𝓝 0) := by
  classical
  let f := fun n => brownianPredictableVectorGaussianDensity B
    (fun k => h (itoUniformNNTime T (n+1) k)) (itoUniformNNTime T (n+1)) (n+1)
  have hm (n : ℕ) : Measurable (f n) :=
    (brownianPredictableVectorGaussianDensity_measurable_at B P hB
      (fun k => h (itoUniformNNTime T (n+1) k)) (itoUniformNNTime T (n+1))
      (itoUniformNNTime_mono _ _) (fun k => hh _) (n+1)).mono
        ((ginibreBrownianAugmentedFiltration B P hB).le _) le_rfl
  have h2 (n : ℕ) : (∫⁻ ω, ENNReal.ofReal (f n ω)^2 ∂P) ≤
      ENNReal.ofReal (Real.exp (C^2*(T : ℝ))) := by
    have hh2 := brownianPredictableVectorGaussianDensity_lintegral_sq_le B P hB hind
      (fun k => h (itoUniformNNTime T (n+1) k)) (itoUniformNNTime T (n+1))
      (itoUniformNNTime_mono _ _) (by simp [itoUniformNNTime,itoUniformTime])
      (fun k => hh _) C hC (fun k => hb _) (n+1)
    simpa only [f,itoUniformNNTime_end T (n+1) (Nat.succ_pos n)] using hh2
  exact nonnegativeDensities_limit_normalized_of_secondMoment_bound P f hm
    (fun n ω => (brownianPredictableVectorGaussianDensity_pos B _ _ _ ω).le)
    (Real.exp (C^2*(T : ℝ))) (Real.exp_pos _).le h2
    (fun n => brownianPredictableVectorGaussianDensity_lintegral B P hB hind _ _
      (itoUniformNNTime_mono _ _) (fun k => hh _) (n+1)) D hlim

end
end GinibrePoincare
