module

public import GinibrePoincare.Analysis.BrownianOrthogonalContinuousNoise
public import GinibrePoincare.Analysis.GinibreHamiltonianProcessFactorization

@[expose] public section

/-! Unconditional whole-process center/relative independence for the actual
original Brownian-driven global Ginibre solution. -/
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownian_center_relative_processes_independent {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    IndepFun (fun ω t => coordinateSum (ginibreBrownianMaximalProcess n α z B t ω))
      (fun ω t => recenteredConfiguration n (ginibreBrownianMaximalProcess n α z B t ω)) P := by
  exact ginibreBrownian_center_relative_processes_independent_of_noise hn α z hz B P hB hind
    (brownianFamily_actual_continuous_center_recenter_noise_independent hn B P hB hind α)

end
end GinibrePoincare
