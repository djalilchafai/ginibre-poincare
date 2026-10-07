module

public import GinibrePoincare.Analysis.GinibreStochasticGlobalUniqueness
public import GinibrePoincare.Analysis.GinibreHamiltonianTransitionKernel

@[expose] public section

/-! Any actual collision-free global realization of the original Brownian
Volterra equation has the constructed transition law. This is the pathwise
uniqueness endpoint needed by a future analytic-process realization. -/
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreTransitionAnalyticPathLaw_eq_kernel
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (z : {z : Configuration n // CollisionFree z})
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (Y : ℝ → Ω → Configuration n)
    (hY : ∀ᵐ ω ∂P, Continuous (fun t => Y t ω) ∧ Y 0 ω = z.val ∧
      (∀ t : ℝ, 0 ≤ t → CollisionFree (Y t ω)) ∧
      IsGinibreDrivenPath n α (ginibreConfigurationBrownianNoise n B α ω)
        (fun t => Y t ω)) (t : ℝ≥0) :
    P.map (Y (t : ℝ)) = ginibreBrownianTransitionKernel hn α B P t z := by
  rw [ginibreBrownianTransitionKernel_apply_eq_process_law hn α B P hB t z]
  apply Measure.map_congr
  filter_upwards [ginibreBrownianMaximalProcess_global_pathwise_unique
    hn α z.val z.property B P hB hind Y hY] with ω hω
  simpa using hω (t : ℝ) t.property

#print axioms ginibreTransitionAnalyticPathLaw_eq_kernel
end
end GinibrePoincare
