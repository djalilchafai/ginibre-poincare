module

public import GinibrePoincare.Analysis.BrownianStoppingExitMaximalAdaptation
public import GinibrePoincare.Analysis.GinibreHamiltonianMaximalBlowup

@[expose] public section

/-! The canonical maximal process solves the original Brownian Volterra equation before its
actual lifetime. No solution or local-equation certificate is assumed. -/
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem ginibreBrownianMaximalLifetime_pos {Ω : Type*} (n : ℕ) (α : ℝ)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (ω : Ω) :
    0 < ginibreBrownianMaximalLifetime n α z B ω := by
  exact ginibreDrivenMaximalLifetime_pos n α _
    (ginibreBrownianFullContinuousNoise n B α ω).val.continuous
    (ginibreBrownianFullContinuousNoise n B α ω).property z hz

 theorem ginibreBrownianMaximalProcess_equation_ae {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (α : ℝ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsBrownianReal (B i) P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ginibreBrownianMaximalLifetime n α z B ω →
      CollisionFree (ginibreBrownianMaximalProcess n α z B t ω) ∧
      IntervalIntegrable (fun u : ℝ => ginibreLangevinDrift n α
        (ginibreBrownianMaximalProcess n α z B (Real.toNNReal u) ω)) volume 0 (t : ℝ) ∧
      ginibreBrownianMaximalProcess n α z B t ω =
        z + ginibreConfigurationBrownianNoise n B α ω t +
        ∫ u in (0 : ℝ)..(t : ℝ), ginibreLangevinDrift n α
          (ginibreBrownianMaximalProcess n α z B (Real.toNNReal u) ω) := by
  filter_upwards [ginibreBrownianFullContinuousNoise_ae n B P hB α] with ω hω
  intro t ht
  have he := ginibreDrivenMaximalPath_equation (n := n) (α := α)
    (N := (ginibreBrownianFullContinuousNoise n B α ω).val) (z := z)
    (t := (t : ℝ)) ⟨t.coe_nonneg, by simpa only [ginibreBrownianMaximalLifetime, ENNReal.ofReal_coe_nnreal] using ht⟩
  change CollisionFree (ginibreDrivenMaximalValue n α _ z t) ∧ _ ∧ _
  simpa only [ginibreDrivenMaximalPath, Real.toNNReal_coe,
    ginibreBrownianMaximalProcess, hω] using he

end
end GinibrePoincare
