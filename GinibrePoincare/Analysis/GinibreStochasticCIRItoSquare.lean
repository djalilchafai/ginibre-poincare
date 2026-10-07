module

public import GinibrePoincare.Analysis.GinibreStochasticOUItoSquare
public import GinibrePoincare.Analysis.GinibreStochasticCIRConditionalMoment

@[expose] public section

/-! The actual radial process has its square stochastic-integral limit. -/
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem ginibreOneParticleBrownianPath_CIR_square_leftSums {Ω : Type*}
    [MeasurableSpace Ω] (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (α t : ℝ≥0) (z : Configuration 1) :
    TendstoInMeasure P (fun n ω =>
      2*ginibreBrownianOUItoSquareLeftSum Br (2*α) t (z 0).re n ω+
      2*ginibreBrownianOUItoSquareLeftSum Bi (2*α) t (z 0).im n ω) atTop
      (fun ω => ginibreOneParticleRadius (ginibreOneParticleBrownianPath Br Bi α z t ω)-
        ginibreOneParticleRadius z-4*(α : ℝ)*(t : ℝ)+
        4*(α : ℝ)*(∫ s in (0 : ℝ)..t,
          ginibreOneParticleRadius (ginibreOneParticleBrownianPath Br Bi α z s ω))) := by
  let := hBr.isGaussianProcess.isProbabilityMeasure
  let Xr := fun s ω => ginibreBrownianOU Br (2*α) (Real.sqrt ((2*α : ℝ≥0) : ℝ)) (z 0).re s ω
  let Xi := fun s ω => ginibreBrownianOU Bi (2*α) (Real.sqrt ((2*α : ℝ≥0) : ℝ)) (z 0).im s ω
  have hr := ginibre_tendstoInMeasure_const_mul P _ _ 2
    (ginibreBrownianOUItoSquareLeftSum_tendstoInProbability Br P hBr (2*α) t (z 0).re)
  have hi := ginibre_tendstoInMeasure_const_mul P _ _ 2
    (ginibreBrownianOUItoSquareLeftSum_tendstoInProbability Bi P hBi (2*α) t (z 0).im)
  have h := ginibre_tendstoInMeasure_add P _ _ _ _ hr hi
  apply h.congr_right
  filter_upwards [ginibreOneParticleBrownianPath_radius_quadratic_ae Br Bi P hBr hBi α z,
    ginibreBrownianOU_actual_path Br P hBr (2*α) (Real.sqrt ((2*α : ℝ≥0) : ℝ)) (z 0).re,
    ginibreBrownianOU_actual_path Bi P hBi (2*α) (Real.sqrt ((2*α : ℝ≥0) : ℝ)) (z 0).im] with ω hq hrc hic
  have hq' (s : ℝ) : ginibreOneParticleRadius (ginibreOneParticleBrownianPath Br Bi α z s ω) =
      (Xr s ω)^2+(Xi s ω)^2 := by
    simpa only [Xr, Xi, NNReal.coe_mul, NNReal.coe_ofNat] using hq s
  have hI : (∫ s in (0 : ℝ)..t,
      ginibreOneParticleRadius (ginibreOneParticleBrownianPath Br Bi α z s ω)) =
      (∫ s in (0 : ℝ)..t, (Xr s ω)^2)+(∫ s in (0 : ℝ)..t, (Xi s ω)^2) := by
    simp_rw [hq']
    exact intervalIntegral.integral_add (hrc.1.pow 2 |>.intervalIntegrable 0 t)
      (hic.1.pow 2 |>.intervalIntegrable 0 t)
  rw [hq', hI]
  simp only [ginibreOneParticleRadius, Complex.normSq_apply, Xr, Xi, NNReal.coe_mul, NNReal.coe_ofNat]
  ring

 def ginibreOneParticleCIRActualLeftSum {Ω : Type*} (Br Bi : ℝ≥0 → Ω → ℝ)
    (α t : ℝ≥0) (z : Configuration 1) (n : ℕ) : Ω → ℝ := fun ω =>
  2*(∑ i ∈ Finset.range (n+1),
    (ginibreOneParticleBrownianPath Br Bi α z (ginibreUniformTime t n i) ω 0).re*
      (ginibreBrownianNoise Br (Real.sqrt (2*(α : ℝ))) ω (ginibreUniformTime t n (i+1))-
        ginibreBrownianNoise Br (Real.sqrt (2*(α : ℝ))) ω (ginibreUniformTime t n i)))+
  2*(∑ i ∈ Finset.range (n+1),
    (ginibreOneParticleBrownianPath Br Bi α z (ginibreUniformTime t n i) ω 0).im*
      (ginibreBrownianNoise Bi (Real.sqrt (2*(α : ℝ))) ω (ginibreUniformTime t n (i+1))-
        ginibreBrownianNoise Bi (Real.sqrt (2*(α : ℝ))) ω (ginibreUniformTime t n i)))

 theorem ginibreOneParticleCIRActualLeftSum_tendstoInProbability {Ω : Type*}
    [MeasurableSpace Ω] (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (α t : ℝ≥0) (z : Configuration 1) :
    TendstoInMeasure P (fun n => ginibreOneParticleCIRActualLeftSum Br Bi α t z n) atTop
      (fun ω => ginibreOneParticleRadius (ginibreOneParticleBrownianPath Br Bi α z t ω)-
        ginibreOneParticleRadius z-4*(α : ℝ)*(t : ℝ)+
        4*(α : ℝ)*(∫ s in (0 : ℝ)..t,
          ginibreOneParticleRadius (ginibreOneParticleBrownianPath Br Bi α z s ω))) := by
  apply (ginibreOneParticleBrownianPath_CIR_square_leftSums Br Bi P hBr hBi α t z).congr_left
  intro n
  filter_upwards [ginibreOneParticleBrownianPath_projections Br Bi P hBr hBi α z] with ω hp
  simp only [ginibreOneParticleCIRActualLeftSum, ginibreBrownianOUItoSquareLeftSum,
    NNReal.coe_mul, NNReal.coe_ofNat]
  simp_rw [← (hp _).1, ← (hp _).2]

end
end GinibrePoincare
