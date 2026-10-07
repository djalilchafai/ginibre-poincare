module

public import GinibrePoincare.Analysis.GinibreHamiltonianCenterFunctional

@[expose] public section

/-! Measurable functional transport of whole center and relative process independence. -/
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 theorem ginibreCenterOUPath_measurable (n : ℕ) (α : ℝ) (z : Configuration n) :
    @Measurable C(ℝ, ℂ) (ℝ≥0 → ℂ) (borel _) _
      (fun N t => ginibreCenterOUValue n α z t N) := by
  letI : MeasurableSpace C(ℝ, ℂ) := borel _
  letI : BorelSpace C(ℝ, ℂ) := ⟨rfl⟩
  apply measurable_pi_lambda
  intro t
  exact ginibreCenterOUValue_measurable n α z t

 theorem ginibreDrivenCanonicalPath_measurable {n : ℕ} (hn : 0 < n)
    (α : ℝ) (z : Configuration n) :
    Measurable (fun N : GinibreContinuousNoise n => fun t : ℝ≥0 => ginibreDrivenMaximalValue n α N.val z t) := by
  apply measurable_pi_lambda
  intro t
  exact ginibreDrivenMaximalValue_measurable hn α z t

 theorem ginibreBrownian_center_relative_processes_independent_of_noise {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (hNoise : @IndepFun Ω C(ℝ, ℂ) (GinibreContinuousNoise n) _ (borel _) _
      (fun ω => ginibreContinuousNoiseCenter n (ginibreBrownianFullContinuousNoise n B α ω))
      (fun ω => ginibreContinuousNoiseRecenter n (ginibreBrownianFullContinuousNoise n B α ω)) P) :
    IndepFun (fun ω t => coordinateSum (ginibreBrownianMaximalProcess n α z B t ω))
      (fun ω t => recenteredConfiguration n (ginibreBrownianMaximalProcess n α z B t ω)) P := by
  letI : MeasurableSpace C(ℝ, ℂ) := borel _
  letI : BorelSpace C(ℝ, ℂ) := ⟨rfl⟩
  have h := hNoise.comp (ginibreCenterOUPath_measurable n α z)
    (ginibreDrivenCanonicalPath_measurable hn α (recenteredConfiguration n z))
  have hS : (fun ω t => ginibreCenterOUValue n α z t
      (ginibreContinuousNoiseCenter n (ginibreBrownianFullContinuousNoise n B α ω))) =ᵐ[P]
      (fun ω t => coordinateSum (ginibreBrownianMaximalProcess n α z B t ω)) := by
    filter_upwards [ginibreBrownian_center_OU_factorization hn α z hz B P hB hind] with ω hω
    funext t
    exact (hω t).symm
  have hW : (fun ω t => ginibreDrivenMaximalValue n α
      (ginibreContinuousNoiseRecenter n (ginibreBrownianFullContinuousNoise n B α ω)).val
      (recenteredConfiguration n z) t) =ᵐ[P]
      (fun ω t => recenteredConfiguration n (ginibreBrownianMaximalProcess n α z B t ω)) := by
    filter_upwards [ginibreBrownian_recentered_canonical_factorization hn α z hz B P hB hind] with ω hω
    funext t
    exact (hω.2 t).symm
  exact h.congr hS hW

end
end GinibrePoincare
