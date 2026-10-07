module

public import GinibrePoincare.Analysis.GinibreStochasticOUQuadraticConditional

@[expose] public section

/-! # First conditional moment of the actual radial process -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem ginibreOneParticleBrownianPath_radius_quadratic_ae {Ω : Type*} [MeasurableSpace Ω]
    (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (α : ℝ≥0) (z : Configuration 1) :
    ∀ᵐ ω ∂P, ∀ t : ℝ,
      ginibreOneParticleRadius (ginibreOneParticleBrownianPath Br Bi α z t ω) =
        (ginibreBrownianOU Br (2*α : ℝ≥0) (Real.sqrt (2*(α : ℝ))) (z 0).re t ω)^2+
        (ginibreBrownianOU Bi (2*α : ℝ≥0) (Real.sqrt (2*(α : ℝ))) (z 0).im t ω)^2 := by
  filter_upwards [ginibreOneParticleBrownianPath_projections Br Bi P hBr hBi α z] with ω hω
  intro t
  unfold ginibreOneParticleRadius
  rw [Complex.normSq_apply, (hω t).1, (hω t).2]
  simp only [NNReal.coe_mul, NNReal.coe_ofNat]
  ring

 theorem ginibreOneParticleBrownianPath_radius_integrable {Ω : Type*} [MeasurableSpace Ω]
    (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (α t : ℝ≥0) (z : Configuration 1) :
    Integrable (fun ω => ginibreOneParticleRadius (ginibreOneParticleBrownianPath Br Bi α z t ω)) P := by
  have h := (ginibreBrownianOU_memLp_two Br P hBr (2*α) t (z 0).re).integrable_sq.add
    (ginibreBrownianOU_memLp_two Bi P hBi (2*α) t (z 0).im).integrable_sq
  apply h.congr
  filter_upwards [ginibreOneParticleBrownianPath_radius_quadratic_ae Br Bi P hBr hBi α z] with ω hω
  simpa only [NNReal.coe_mul, NNReal.coe_ofNat, Pi.add_apply] using (hω t).symm

 theorem ginibreOneParticleBrownianPath_CIR_conditional_mean {Ω : Type*} [MeasurableSpace Ω]
    (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (hind : IndepFun (fun ω u => Br u ω) (fun ω u => Bi u ω) P)
    (α s t : ℝ≥0) (z : Configuration 1) :
    P[(fun ω => ginibreOneParticleRadius (ginibreOneParticleBrownianPath Br Bi α z (s+t) ω)) |
      ginibrePlanarBrownianPastMeasurableSpace Br Bi s] =ᵐ[P]
      (fun ω => 1+(ginibreOUDecay (2*α) t)^2*
        (ginibreOneParticleRadius (ginibreOneParticleBrownianPath Br Bi α z s ω)-1)) := by
  have hq := ginibreOneParticleBrownianPath_radius_quadratic_ae Br Bi P hBr hBi α z
  have he := hq.mono (fun ω hω => hω (s+t))
  have h := ginibreBrownianOU_planar_quadratic_conditional Br Bi P hBr hBi hind (2*α) s t (z 0).re (z 0).im
  have he' := he
  simp only [NNReal.coe_mul, NNReal.coe_ofNat] at he'
  apply ((condExp_congr_ae (m := ginibrePlanarBrownianPastMeasurableSpace Br Bi s) he').trans h).trans
  filter_upwards [hq] with ω hω
  rw [ginibreOUVariance_coe, hω s]
  simp only [NNReal.coe_mul, NNReal.coe_ofNat]
  ring

end
end GinibrePoincare
