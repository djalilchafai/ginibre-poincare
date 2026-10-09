module

public import GinibrePoincare.Analysis.GinibreDrivenPathLocalUniqueness
public import Mathlib.Probability.BrownianMotion.Basic

@[expose] public section

/-! # Actual local collision-free Brownian-driven Ginibre paths

The cumulative noise has the paper's coefficient √(2α/n²). Independence of
coordinates is unnecessary for this pathwise existence theorem; it is needed
for the associated isotropic diffusion law.
-/
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 def ginibreConfigurationBrownianNoise {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ) (ω : Ω) (t : ℝ) : Configuration n :=
  fun j => Real.sqrt (2*α/(n : ℝ)^2) •
    ((B (j, 0) t.toNNReal ω : ℂ)+Complex.I*(B (j, 1) t.toNNReal ω : ℂ))

 theorem ginibreConfigurationBrownianNoise_actual {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsBrownianReal (B i) P) (α : ℝ) :
    ∀ᵐ ω ∂P, Continuous (ginibreConfigurationBrownianNoise n B α ω) ∧
      ginibreConfigurationBrownianNoise n B α ω 0 = 0 := by
  have hc : ∀ᵐ ω ∂P, ∀ i, Continuous (fun t => B i t ω) :=
    ae_all_iff.mpr (fun i => (hB i).cont)
  have hz : ∀ᵐ ω ∂P, ∀ i, B i 0 ω = 0 :=
    ae_all_iff.mpr (fun i => (hB i).eval_zero_ae_eq_zero)
  filter_upwards [hc, hz] with ω hc hz
  constructor
  · apply continuous_pi
    intro j
    exact ((Complex.continuous_ofReal.comp ((hc (j, 0)).comp continuous_real_toNNReal)).add
      (continuous_const.mul (Complex.continuous_ofReal.comp
        ((hc (j, 1)).comp continuous_real_toNNReal)))).const_smul (Real.sqrt (2*α/(n : ℝ)^2))
  · ext j
    simp [ginibreConfigurationBrownianNoise, hz]

 theorem ginibreBrownian_driven_local_collision_free_exists {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsBrownianReal (B i) P) (α : ℝ)
    (z : Configuration n) (hz : CollisionFree z) :
    ∀ᵐ ω ∂P, ∃ τ > (0 : ℝ), ∃ X : ℝ → Configuration n,
      ContinuousOn X (Icc 0 τ) ∧ X 0 = z ∧
      ∀ t ∈ Icc 0 τ, CollisionFree (X t) ∧
        IntervalIntegrable (fun u => ginibreLangevinDrift n α (X u)) volume 0 t ∧
        X t = z+ginibreConfigurationBrownianNoise n B α ω t+
          ∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (X u) := by
  filter_upwards [ginibreConfigurationBrownianNoise_actual n B P hB α] with ω hω
  exact ginibreDrivenPath_continuous_noise_local_exists n α z hz _ hω.1 hω.2

end
end GinibrePoincare
