module

public import GinibrePoincare.Analysis.GinibreStochasticOneParticleMarkov

@[expose] public section

/-! # Actual squared-radius laws of the one-particle driven Ginibre solution

These laws are pushforwards of the proved planar Gaussian transition. The
initial planar state is retained explicitly; autonomy as a function of its
radius requires a separate rotation-invariance argument.
-/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 def ginibreOneParticleRadius (z : Configuration 1) : ℝ := Complex.normSq (z 0)

 theorem ginibreOneParticleRadius_continuous : Continuous ginibreOneParticleRadius := by
  unfold ginibreOneParticleRadius
  fun_prop

 def ginibreOneParticleRadiusTransition (α t : ℝ≥0) (z : Configuration 1) : Measure ℝ :=
  (ginibreOneParticleOUTransition α t z).map ginibreOneParticleRadius

 theorem ginibreOneParticleBrownianPath_radius_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (hind : IndepFun (fun ω u => Br u ω) (fun ω u => Bi u ω) P)
    (α t : ℝ≥0) (z : Configuration 1) :
    HasLaw (fun ω => ginibreOneParticleRadius (ginibreOneParticleBrownianPath Br Bi α z t ω))
      (ginibreOneParticleRadiusTransition α t z) P := by
  have hr : HasLaw ginibreOneParticleRadius
      ((ginibreOneParticleOUTransition α t z).map ginibreOneParticleRadius)
      (ginibreOneParticleOUTransition α t z) :=
    ⟨ginibreOneParticleRadius_continuous.measurable.aemeasurable, rfl⟩
  exact hr.comp (ginibreOneParticleBrownianPath_hasLaw Br Bi P hBr hBi hind α t z)

 theorem ginibreOneParticleBrownianPath_radius_conditional_law {Ω : Type*}
    [MeasurableSpace Ω] (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (hind : IndepFun (fun ω u => Br u ω) (fun ω u => Bi u ω) P)
    (α s t : ℝ≥0) (z : Configuration 1)
    (f : ℝ → ℝ) (hf : Measurable f) (C : ℝ) (hbound : ∀ y, ‖f y‖ ≤ C) :
    P[(fun ω => f (ginibreOneParticleRadius (ginibreOneParticleBrownianPath Br Bi α z (s+t) ω))) |
      ginibrePlanarBrownianPastMeasurableSpace Br Bi s] =ᵐ[P]
      (fun ω => ∫ r, f r ∂ginibreOneParticleRadiusTransition α t
        (ginibreOneParticleBrownianPath Br Bi α z s ω)) := by
  have h := ginibreOneParticleBrownianPath_whole_past_markov Br Bi P hBr hBi hind α s t z
    (f ∘ ginibreOneParticleRadius) (hf.comp ginibreOneParticleRadius_continuous.measurable)
    C (fun y => hbound _)
  apply h.trans
  apply Filter.Eventually.of_forall
  intro ω
  dsimp only
  unfold ginibreOneParticleRadiusTransition
  rw [integral_map ginibreOneParticleRadius_continuous.measurable.aemeasurable
    hf.stronglyMeasurable.aestronglyMeasurable]
  rfl

end
end GinibrePoincare
