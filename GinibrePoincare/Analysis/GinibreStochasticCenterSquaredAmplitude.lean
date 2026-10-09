module

public import GinibrePoincare.Analysis.GinibreStochasticCenterCIRNoiseCoefficient
public import GinibrePoincare.Analysis.GinibreStochasticCIRCoefficientProcess

@[expose] public section

/-! The genuine localized CIR amplitude is bounded, continuous and adapted:
all stochastic integral coefficient hypotheses follow from actual compact localization. -/
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000

theorem ginibreBrownianHamiltonianStoppedProcess_center_CIR_amplitude_properties
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (R : ℝ) (hR : ginibreHamiltonian n z ≤ R) (T : ℝ≥0) :
    let a := fun t ω => Real.sqrt ((8*α/(n : ℝ))*(ginibreCenterSquared n)
      (ginibreBrownianHamiltonianStoppedProcess n α z B R T t ω))
    StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) a ∧
    (∀ ω, Continuous (fun t => a t ω)) ∧
    ∃ C > (0 : ℝ), ∀ t ω, ‖a t ω‖ ≤ C := by
  dsimp only
  let f : Configuration n → ℝ := fun x => Real.sqrt ((8*α/(n : ℝ))*(ginibreCenterSquared n) x)
  have hf : Continuous f := Real.continuous_sqrt.comp
    (continuous_const.mul (contDiff_ginibreCenterSquared n).continuous)
  have hAdapt := ginibreBrownianHamiltonianStoppedProcess_stronglyAdapted hn α z hz B P hB R hR T
  have hCont := ginibreBrownianHamiltonianStoppedProcess_continuous hn α z hz B R hR T
  refine ⟨fun t => (hf.measurable.comp (hAdapt t).measurable).stronglyMeasurable,
    fun ω => hf.comp (hCont ω),?_⟩
  obtain ⟨C, hC, hb⟩ := ((ginibreHamiltonianSublevel_isCompact hn R).image hf).isBounded.exists_pos_norm_le
  refine ⟨C, hC, fun t ω => hb _ ?_⟩
  exact ⟨_, ginibreBrownianHamiltonianStoppedProcess_range hn α z hz B R hR T t ω, rfl⟩
end
end GinibrePoincare
