module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsStationaryLaw
public import GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsLSICoupling
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]
set_option backward.isDefEq.respectTransparency false

theorem bakryEmeryOriginalCompactDriver_eq_BrownianNoisePath
    (n : ℕ) (hn : 0 < n) (B : (Fin n×Fin 2) → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) (hB : ∀ i, IsBrownianReal (B i) P) (T : ℝ≥0) :
    bakryEmeryOriginalCompactDriver n B T =ᵐ[P]
      (fun ω => Real.sqrt 2 • bakryEmeryBrownianNoisePath (T:ℝ) B ω) := by
  have hn0 : (n:ℝ)^2 ≠ 0 := by positivity
  have hscale : 2*(n:ℝ)^2/(n:ℝ)^2 = 2 := by field_simp
  filter_upwards [bakryEmeryOriginalCompactDriver_ae_eq n B P hB T,
    bakryEmeryBrownianNoisePath_actual (T:ℝ) B P hB] with ω hω hpath
  apply ContinuousMap.ext
  intro t
  rw [hω t]
  change configurationEuclideanEquiv n (ginibreConfigurationBrownianNoise n B ((n:ℝ)^2) ω t) =
    Real.sqrt 2 • bakryEmeryBrownianNoisePath (T:ℝ) B ω t
  rw [hpath t]
  apply PiLp.ext
  intro i
  rcases i with ⟨j,k⟩
  fin_cases k <;>
    simp [ginibreConfigurationBrownianNoise,bakryEmeryBrownianNoiseReal,
      configurationEuclideanEquiv_apply_zero,configurationEuclideanEquiv_apply_one,hscale]

theorem bakryEmeryGibbsActualEndpoint_eq_BrownianEndpoint
    (n : ℕ) (hn : 0 < n) (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W)
    (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n×Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2))
    (B : (Fin n×Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsBrownianReal (B i) P) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ z : Configuration n,
      configurationEuclideanEquiv n (bakryEmeryGibbsActualEndpoint W hW κ hκ hc T B (z,ω)) =
        bakryEmeryBrownianEndpoint (W ∘ (configurationEuclideanEquiv n).symm) κ hκ
          (hW.comp (configurationEuclideanEquiv n).symm.contDiff) hc
          (configurationEuclideanEquiv n z) T T.coe_nonneg B ω := by
  filter_upwards [bakryEmeryOriginalCompactDriver_eq_BrownianNoisePath n hn B P hB T] with ω hω
  intro z
  simp only [bakryEmeryGibbsActualEndpoint,bakryEmeryGibbsPath,ContinuousMap.coe_mk,
    ContinuousLinearEquiv.apply_symm_apply,bakryEmeryBrownianEndpoint,
    bakryEmeryLangevinPath,bakryEmeryLangevinEndpoint,hω]

#print axioms bakryEmeryGibbsActualEndpoint_eq_BrownianEndpoint
#print axioms bakryEmeryOriginalCompactDriver_eq_BrownianNoisePath
end
end GinibrePoincare
