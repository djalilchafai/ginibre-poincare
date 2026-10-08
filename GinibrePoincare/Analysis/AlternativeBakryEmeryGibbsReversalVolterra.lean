module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsReversalStopped
@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000

theorem bakryEmeryGibbsConfigurationDrift_continuous {n : ℕ}
    (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W) :
    Continuous (bakryEmeryGibbsConfigurationDrift W) := by
  apply continuous_pi
  intro j
  exact ((Complex.continuous_ofReal.comp ((hW.continuous_fderiv (by norm_num)).clm_apply continuous_const)).neg).sub
    (continuous_const.mul (Complex.continuous_ofReal.comp ((hW.continuous_fderiv (by norm_num)).clm_apply continuous_const)))

/-- The actual Girsanov-corrected coordinate Brownian driver converts every
reference OU prefix into the concrete ordinary gradient equation. -/
theorem bakryEmeryGibbsOU_correctedBrownian_volterra {Ω : Type*} {n : ℕ}
    (hn : 0 < n) (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (Y : ℝ≥0 → Ω → Configuration n) (sample : Ω) (z : Configuration n) (θ : ℝ≥0)
    (hYC : Continuous (fun t => Y t sample))
    (hN0 : ginibreConfigurationBrownianNoise n B ((n : ℝ)^2) sample 0 = 0)
    (hEq : ∀ t ≤ θ, Y t sample = z + ginibreConfigurationBrownianNoise n B ((n : ℝ)^2) sample t +
      ∫ s in (0 : ℝ)..(t : ℝ), (-2*(n : ℝ)) • Y s.toNNReal sample) :
    ∀ t ≤ θ, Y t sample = z + ginibreConfigurationBrownianNoise n
      (fun i r sample => B i r sample - B i 0 sample - ∫ s in (0 : ℝ)..(r : ℝ),
        bakryEmeryGibbsPotentialTilt n ((n : ℝ)^2) (bakryEmeryGibbsRelativePotential W)
          (Y s.toNNReal sample) i) ((n : ℝ)^2) sample t +
      ∫ s in (0 : ℝ)..(t : ℝ), bakryEmeryGibbsConfigurationDrift W (Y s.toNNReal sample) := by
  let y : ℝ → Configuration n := fun s => Y s.toNNReal sample
  have hy : Continuous y := hYC.comp continuous_real_toNNReal
  have hS : ContDiff ℝ 2 (bakryEmeryGibbsRelativePotential W) :=
    hW.sub (contDiff_const.mul (contDiff_configurationNormSq.of_le (by simp)))
  have hF : Continuous (fun s : ℝ => fun i =>
      bakryEmeryGibbsPotentialTilt n ((n : ℝ)^2) (bakryEmeryGibbsRelativePotential W) (y s) i) := by
    apply continuous_pi
    intro i
    exact (bakryEmeryGibbsPotentialTilt_continuous n ((n : ℝ)^2) _ hS i).comp hy
  intro t ht
  have hiD : IntervalIntegrable (fun s => bakryEmeryGibbsConfigurationDrift W (y s)) volume 0 (t : ℝ) := ((bakryEmeryGibbsConfigurationDrift_continuous W hW).comp hy).intervalIntegrable 0 (t : ℝ)
  have hiOU : IntervalIntegrable (fun s => (-2*(n : ℝ)) • y s) volume 0 (t : ℝ) := (hy.const_smul (-2*(n : ℝ))).intervalIntegrable 0 (t : ℝ)
  have hnoise := ginibreCorrectedBrownianNoise_eq n ((n : ℝ)^2) B
    (fun i r sample => bakryEmeryGibbsPotentialTilt n ((n : ℝ)^2)
      (bakryEmeryGibbsRelativePotential W) (Y r sample) i) sample (t : ℝ) t.property
      (hF.intervalIntegrable 0 t)
  rw [hN0, sub_zero] at hnoise
  have hI : (∫ s in (0 : ℝ)..(t : ℝ), ginibreBrownianEmbeddingCLM n ((n : ℝ)^2)
      (fun i => bakryEmeryGibbsPotentialTilt n ((n : ℝ)^2)
        (bakryEmeryGibbsRelativePotential W) (Y s.toNNReal sample) i)) =
      (∫ s in (0 : ℝ)..(t : ℝ), bakryEmeryGibbsConfigurationDrift W (y s)) -
        ∫ s in (0 : ℝ)..(t : ℝ), (-2*(n : ℝ)) • y s := by
    rw [← intervalIntegral.integral_sub hiD hiOU]
    apply intervalIntegral.integral_congr
    intro s hs
    exact bakryEmeryGibbsConfigurationTilt_eq_drift hn W (hW.differentiable (by norm_num)) (y s)
  rw [hI] at hnoise
  rw [hnoise, hEq t ht]
  change _ = _
  dsimp only [y]
  abel

#print axioms bakryEmeryGibbsConfigurationDrift_continuous
#print axioms bakryEmeryGibbsOU_correctedBrownian_volterra
end
end GinibrePoincare
