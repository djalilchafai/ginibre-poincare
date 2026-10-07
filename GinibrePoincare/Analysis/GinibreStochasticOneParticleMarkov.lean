module

public import GinibrePoincare.Analysis.GinibreStochasticOUPlanarMarkov
public import GinibrePoincare.Analysis.GinibreStochasticOneParticleLaw

@[expose] public section

/-! # Whole-past Markov property of the actual one-particle Ginibre solution -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem ginibreOneParticleBrownianPath_whole_past_markov {Ω : Type*}
    [MeasurableSpace Ω] (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (hind : IndepFun (fun ω u => Br u ω) (fun ω u => Bi u ω) P)
    (α s t : ℝ≥0) (z : Configuration 1)
    (f : Configuration 1 → ℝ) (hf : Measurable f) (C : ℝ) (hbound : ∀ y, ‖f y‖ ≤ C) :
    P[(fun ω => f (ginibreOneParticleBrownianPath Br Bi α z (s+t) ω)) |
      ginibrePlanarBrownianPastMeasurableSpace Br Bi s] =ᵐ[P]
      (fun ω => ∫ y, f y ∂ginibreOneParticleOUTransition α t
        (ginibreOneParticleBrownianPath Br Bi α z s ω)) := by
  let F : ℝ × ℝ → Configuration 1 := fun p _ => (p.1 : ℂ) + Complex.I * (p.2 : ℂ)
  let rate : ℝ≥0 := 2 * α
  have hF : Measurable F := by fun_prop
  have h := ginibreBrownianOU_planar_whole_past_markov Br Bi P hBr hBi hind rate s t
    (z 0).re (z 0).im (f ∘ F) (hf.comp hF) C (fun y => hbound (F y))
  have hproj := ginibreOneParticleBrownianPath_projections Br Bi P hBr hBi α z
  have he : (fun ω => f (ginibreOneParticleBrownianPath Br Bi α z (s+t) ω)) =ᵐ[P]
      (fun ω => (f ∘ F) (ginibreBrownianOU Br rate (Real.sqrt (rate : ℝ)) (z 0).re (s+t) ω,
        ginibreBrownianOU Bi rate (Real.sqrt (rate : ℝ)) (z 0).im (s+t) ω)) := by
    filter_upwards [hproj] with ω hω
    congr 1
    ext j
    have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
    subst j
    apply Complex.ext
    · simpa [F, rate] using (hω (s+t)).1
    · simpa [F, rate] using (hω (s+t)).2
  apply ((condExp_congr_ae (m := ginibrePlanarBrownianPastMeasurableSpace Br Bi s) he).trans h).trans
  filter_upwards [hproj] with ω hω
  unfold ginibreOneParticleOUTransition
  rw [integral_map hF.aemeasurable hf.stronglyMeasurable.aestronglyMeasurable]
  have hr := (hω s).1
  have hi := (hω s).2
  simp only [Function.comp_apply]
  simpa only [rate, NNReal.coe_mul, NNReal.coe_ofNat, hr, hi] using
    (rfl : (∫ y, f (F y) ∂((ginibreOUTransition rate t
      (ginibreBrownianOU Br rate (Real.sqrt (rate : ℝ)) (z 0).re s ω)).prod
      (ginibreOUTransition rate t (ginibreBrownianOU Bi rate (Real.sqrt (rate : ℝ)) (z 0).im s ω)))) = _)

end
end GinibrePoincare
