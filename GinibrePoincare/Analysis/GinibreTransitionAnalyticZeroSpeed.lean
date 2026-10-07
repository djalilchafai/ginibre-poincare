module

public import GinibrePoincare.Analysis.GinibreStochasticCenterZeroSpeed
public import GinibrePoincare.Analysis.GinibreFullSemigroupPaperSpeed

@[expose] public section

/-! The actual original transition and analytic evolution coincide at zero
paper speed on every symmetric L² value. -/
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000

theorem ginibreBrownian_zero_speed_transition_integral
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (f : Configuration n → ℝ) (t : ℝ≥0) :
    (∫ ω, f (ginibreBrownianMaximalProcess n 0 z B t ω) ∂P)=f z := by
  have he : (fun ω => f (ginibreBrownianMaximalProcess n 0 z B t ω)) =ᵐ[P] (fun _ => f z) :=
    (ginibreBrownianMaximalProcess_zero_speed_constant hn z hz B P hB hind).mono fun ω hω => congrArg f (hω t)
  rw [integral_congr_ae he]
  simp

theorem ginibreFullRealPaperEvolution_zero_speed {n : ℕ} (hn : 0 < n) (t : ℝ≥0) :
    ginibreFullRealPaperEvolution n hn 0 t=1 := by
  ext u
  simp [ginibreFullRealPaperEvolution,ginibrePaperSpeedFactor,ginibreFullRealEvolution,
    ginibreFullEvolution_zero,ginibreFullSymmetricRe_ofReal]

theorem ginibreBrownian_zero_speed_analytic_transition
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (u : ginibreFullSymmetricValues n) (t : ℝ≥0) :
    (∫ ω, u.val (ginibreBrownianMaximalProcess n 0 z B t ω) ∂P)=
      (ginibreFullRealPaperEvolution n hn 0 t u).val z := by
  rw [ginibreFullRealPaperEvolution_zero_speed hn t]
  exact ginibreBrownian_zero_speed_transition_integral hn z hz B P hB hind u.val t

#print axioms ginibreBrownian_zero_speed_transition_integral
#print axioms ginibreFullRealPaperEvolution_zero_speed
#print axioms ginibreBrownian_zero_speed_analytic_transition
end
end GinibrePoincare
