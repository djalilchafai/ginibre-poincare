module

public import GinibrePoincare.Analysis.BrownianOrthogonalGlobalPathFactorization
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
local instance (n : ℕ) : MeasurableSpace C(ℝ, Configuration n) := borel _
local instance (n : ℕ) : BorelSpace C(ℝ, Configuration n) := ⟨rfl⟩
local instance : MeasurableSpace C(ℝ, ℂ) := borel _
local instance : BorelSpace C(ℝ, ℂ) := ⟨rfl⟩

/-- The actual canonical path initialized from a configuration sampled at equilibrium. -/
def ginibreEquilibriumPath {Ω : Type*} {n : ℕ} (α : ℝ)
    (z₀ : Configuration n) (hz₀ : CollisionFree z₀)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (p : Configuration n × Ω) : C(ℝ, Configuration n) :=
  ginibreDrivenGlobalPathElement α (ginibreFreeInitialVersion z₀ hz₀ p.1,
    ginibreBrownianFullContinuousNoise n B α p.2)

theorem ginibreEquilibriumPath_measurable {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ) (z₀ : Configuration n) (hz₀ : CollisionFree z₀)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) : Measurable (ginibreEquilibriumPath α z₀ hz₀ B) :=
  (ginibreDrivenGlobalPathElement_measurable hn α).comp
    (((ginibreFreeInitialVersion_measurable z₀ hz₀).comp measurable_fst).prodMk
      ((ginibreBrownianFullContinuousNoise_measurable n B P hB α).comp measurable_snd))

/-- The true relative canonical path uses only the relative initial value and noise. -/
def ginibreRelativeEquilibriumPath {Ω : Type*} {n : ℕ} (α : ℝ)
    (z₀ : Configuration n) (hz₀ : CollisionFree z₀)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (p : Configuration n × Ω) : C(ℝ, Configuration n) :=
  ginibreDrivenGlobalPathElement α
    (ginibreFreeInitialVersion (recenteredConfiguration n z₀) (collisionFree_recentered hz₀)
      (recenteredConfiguration n p.1),
      ginibreContinuousNoiseRecenter n (ginibreBrownianFullContinuousNoise n B α p.2))

theorem ginibreRelativeEquilibriumPath_measurable {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ) (z₀ : Configuration n) (hz₀ : CollisionFree z₀)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) : Measurable (ginibreRelativeEquilibriumPath α z₀ hz₀ B) := by
  have hW : Measurable (recenteredConfiguration n) := by
    convert (recenteredCLM n).continuous.measurable using 1
    funext z
    exact (recenteredCLM_apply n z).symm
  exact (ginibreDrivenGlobalPathElement_measurable hn α).comp
    ((((ginibreFreeInitialVersion_measurable _ _).comp hW).comp measurable_fst).prodMk
      (((ginibreContinuousNoiseRecenter_continuous n).measurable.comp
        (ginibreBrownianFullContinuousNoise_measurable n B P hB α)).comp measurable_snd))

/-- The equilibrium-initialized center and relative canonical functionals are independent. -/
theorem ginibre_equilibrium_OU_relative_functionals_independent {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ) (z₀ : Configuration n) (hz₀ : CollisionFree z₀)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    IndepFun (fun p : Configuration n × Ω => ginibreOUPathElement n α
      (coordinateSum p.1, ginibreContinuousNoiseCenter n (ginibreBrownianFullContinuousNoise n B α p.2)))
      (ginibreRelativeEquilibriumPath α z₀ hz₀ B) ((ginibreMeasure n).prod P) := by
  have hrel : Measurable (fun p : Configuration n × GinibreContinuousNoise n =>
      ginibreDrivenGlobalPathElement α
        (ginibreFreeInitialVersion (recenteredConfiguration n z₀) (collisionFree_recentered hz₀) p.1, p.2)) :=
    (ginibreDrivenGlobalPathElement_measurable hn α).comp
      (((ginibreFreeInitialVersion_measurable _ _).comp measurable_fst).prodMk measurable_snd)
  exact (ginibre_equilibrium_center_relative_inputs_independent hn B P hB hind α).comp
    (ginibreOUPathElement_measurable n α) hrel

end
end GinibrePoincare
