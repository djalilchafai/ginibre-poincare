module

public import GinibrePoincare.Analysis.GinibreStochasticOneParticle
public import GinibrePoincare.Analysis.GinibreDrivenPathOUProjection

@[expose] public section

/-! # Actual real and imaginary OU projections of the one-particle solution -/
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 def ginibreOneParticleRealCLM : Configuration 1 →L[ℝ] ℝ :=
  Complex.reCLM.comp (ContinuousLinearMap.proj 0)
 def ginibreOneParticleImagCLM : Configuration 1 →L[ℝ] ℝ :=
  Complex.imCLM.comp (ContinuousLinearMap.proj 0)

 theorem ginibreOneParticleBrownianPath_projections {Ω : Type*} [MeasurableSpace Ω]
    (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (α : ℝ) (z : Configuration 1) :
    ∀ᵐ ω ∂P, ∀ t : ℝ,
      (ginibreOneParticleBrownianPath Br Bi α z t ω 0).re =
        ginibreBrownianOU Br (2 * α) (Real.sqrt (2 * α)) (z 0).re t ω ∧
      (ginibreOneParticleBrownianPath Br Bi α z t ω 0).im =
        ginibreBrownianOU Bi (2 * α) (Real.sqrt (2 * α)) (z 0).im t ω := by
  filter_upwards [hBr.cont, hBi.cont] with ω hcr hci
  let N := ginibreOneParticleBrownianNoise Br Bi α ω
  have hN : Continuous N := by
    apply continuous_pi
    intro j
    exact ((Complex.continuous_ofReal.comp (hcr.comp continuous_real_toNNReal)).add
      (continuous_const.mul (Complex.continuous_ofReal.comp
        (hci.comp continuous_real_toNNReal)))).const_smul (Real.sqrt (2 * α))
  have hre : (fun s => ginibreOneParticleRealCLM (N s)) =
      ginibreBrownianNoise Br (Real.sqrt (2 * α)) ω := by
    funext s
    simp [ginibreOneParticleRealCLM, N, ginibreOneParticleBrownianNoise,
      ginibreBrownianNoise, Complex.mul_re]
  have him : (fun s => ginibreOneParticleImagCLM (N s)) =
      ginibreBrownianNoise Bi (Real.sqrt (2 * α)) ω := by
    funext s
    simp [ginibreOneParticleImagCLM, N, ginibreOneParticleBrownianNoise,
      ginibreBrownianNoise, Complex.mul_im]
  intro t
  constructor
  · have h := drivenOUPath_continuousLinearMap ginibreOneParticleRealCLM (2 * α) z N hN t
    rw [hre] at h
    exact h
  · have h := drivenOUPath_continuousLinearMap ginibreOneParticleImagCLM (2 * α) z N hN t
    rw [him] at h
    exact h

end
end GinibrePoincare
