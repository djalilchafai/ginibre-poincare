module

public import GinibrePoincare.Analysis.BrownianIntegralGaussianFiniteLaw
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- An actual probability limit of variables with the same actual law keeps
that law, by genuine weak convergence and uniqueness. -/
theorem actualConstantLaw_of_tendstoInMeasure
    {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure E) [IsProbabilityMeasure μ]
    (S : ℕ → Ω → E) (hS : ∀ n, HasLaw (S n) μ P) (L : Ω → E)
    (hL : TendstoInMeasure P S atTop L) : HasLaw L μ P := by
  have hd := hL.tendstoInDistribution (fun n => (hS n).aemeasurable)
  have hid : HasLaw (id : E → E) μ μ := ⟨measurable_id.aemeasurable,Measure.map_id⟩
  have hdid : TendstoInDistribution S atTop (id : E → E) (fun _ => P) μ :=
    tendstoInDistribution_of_identDistrib 0
    (fun n => (hS 0).identDistrib (hS n)) ((hS 0).identDistrib hid)
  have he := tendstoInDistribution_unique S hd hdid
  rw [Measure.map_id] at he
  exact ⟨hd.aemeasurable_limit,he⟩

/-- Gaussian endpoint law of a genuine probability limit of the actual
coordinate sums driven by an adapted unit field. -/
theorem brownianUnitField_integral_limit_gaussian
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (u : ℝ≥0 → Ω → EuclideanSpace ℝ ι)
    (hu : ∀ s, @Measurable Ω (EuclideanSpace ℝ ι)
      (ginibreBrownianAugmentedFiltration B P hB s) _ (u s))
    (hunit : ∀ s ω, ‖u s ω‖ = 1) (i : ι) (T : ℝ≥0) (L : Ω → ℝ)
    (hL : TendstoInMeasure P (fun n ω =>
      ∑ j, brownianUniformLeftSum (B j) (fun s ω => u s ω j) T (n+1) ω) atTop L) :
    HasLaw L (gaussianReal 0 T) P :=
  actualConstantLaw_of_tendstoInMeasure P (gaussianReal 0 T) _
    (fun n => brownianUnitField_uniform_sum_gaussian B P hB hind u hu hunit i T (n+1) (Nat.succ_pos n)) L hL

end
end GinibrePoincare
