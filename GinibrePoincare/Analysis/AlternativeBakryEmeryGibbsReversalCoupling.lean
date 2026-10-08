module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsReversalPathFactory
public import GinibrePoincare.Analysis.AlternativeBakryEmeryLangevinCorrectedDriver
public import GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsReversalSurvival
@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The normalized actual OU process solves its continuous-driver equation
on every sample, including the specified Brownian-null-set fallback. -/
theorem bakryEmeryGibbsOU_normalized_equation {Ω : Type*} {n : ℕ} (hn : 0 < n)
    (z : Configuration n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (sample : Ω) (t : ℝ≥0) :
    ginibreHamiltonianOUReferenceProcess n ((n : ℝ)^2) z B t sample =
      z+(ginibreBrownianFullContinuousNoise n B ((n : ℝ)^2) sample).val t+
        ∫ s in (0 : ℝ)..(t : ℝ), (-2*(n : ℝ)) •
          ginibreHamiltonianOUReferenceProcess n ((n : ℝ)^2) z B s.toNNReal sample := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hcoef : 2*(n : ℝ)^2/(n : ℝ) = 2*(n : ℝ) := by field_simp
  have h := drivenOUPath_integral_equation (2*(n : ℝ)^2/(n : ℝ)) z
    (ginibreBrownianFullContinuousNoise n B ((n : ℝ)^2) sample).val
    (ginibreBrownianFullContinuousNoise n B ((n : ℝ)^2) sample).val.continuous (t : ℝ)
  change ginibreHamiltonianOUReferenceProcess n ((n : ℝ)^2) z B t sample = _ at h
  rw [h]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hs0 : 0 ≤ s := (show s ∈ Icc (0 : ℝ) (t : ℝ) by simpa [uIcc_of_le t.property] using hs).1
  unfold ginibreHamiltonianOUReferenceProcess ginibreHamiltonianOUValue
  dsimp only
  rw [Real.coe_toNNReal _ hs0, hcoef]
  congr 1
  ring

/-- Actual stopped OU coupled to the actual selected ordinary-gradient
path through its literal tilt driver. No solution-identification certificate
is assumed. -/
theorem bakryEmeryGibbs_actual_stopped_coupling {Ω : Type*} {n : ℕ} (hn : 0 < n)
    (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W) (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2))
    (z : Configuration n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (Y : ℝ≥0 → Ω → Configuration n) (hYC : ∀ sample, Continuous (fun t => Y t sample))
    (θ : Ω → ℝ≥0) (hθ : ∀ sample, θ sample ≤ T)
    (hStopped : ∀ t sample, Y t sample =
      ginibreHamiltonianOUReferenceProcess n ((n : ℝ)^2) z B (min t (θ sample)) sample) :
    ∀ sample t (ht : t ≤ θ sample),
      bakryEmeryGibbsPath W hW κ hκ hc T
        (z,bakryEmeryCorrectedCompactDriver n W hW B T Y hYC sample)
        ⟨(t : ℝ),⟨t.property,by exact_mod_cast ht.trans (hθ sample)⟩⟩ =
      ginibreHamiltonianOUReferenceProcess n ((n : ℝ)^2) z B t sample := by
  intro sample
  let y : ℝ → Configuration n := fun s => Y s.toNNReal sample
  let N := bakryEmeryCorrectedCompactDriver n W hW B T Y hYC sample
  have hy : Continuous y := (hYC sample).comp continuous_real_toNNReal
  have hEq : ∀ t ∈ Icc (0 : ℝ) (θ sample : ℝ), y t = z+
      (configurationEuclideanEquiv n).symm (bkWeightedExtension T T.property N t)+
      ∫ s in (0 : ℝ)..t, bakryEmeryGibbsConfigurationDrift W (y s) := by
    intro t ht
    have htt : t.toNNReal ≤ θ sample := Real.toNNReal_le_iff_le_coe.mpr ht.2
    have hs : y t = ginibreHamiltonianOUReferenceProcess n ((n : ℝ)^2) z B t.toNNReal sample := by
      dsimp only [y]
      rw [hStopped, min_eq_left htt]
    have hOU := bakryEmeryGibbsOU_normalized_equation hn z B sample t.toNNReal
    rw [Real.coe_toNNReal _ ht.1] at hOU
    have hIOU : (∫ s in (0 : ℝ)..t, (-2*(n : ℝ)) •
        ginibreHamiltonianOUReferenceProcess n ((n : ℝ)^2) z B s.toNNReal sample) =
        ∫ s in (0 : ℝ)..t, (-2*(n : ℝ)) • y s := by
      apply intervalIntegral.integral_congr
      intro s hsI
      have hsT : s.toNNReal ≤ θ sample := Real.toNNReal_le_iff_le_coe.mpr
        ((show s ∈ Icc (0 : ℝ) t by simpa [uIcc_of_le ht.1] using hsI).2.trans ht.2)
      dsimp only [y]
      rw [hStopped, min_eq_left hsT]
    have hiD : IntervalIntegrable (fun s => bakryEmeryGibbsConfigurationDrift W (y s)) volume 0 t :=
      ((bakryEmeryGibbsConfigurationDrift_continuous W hW).comp hy).intervalIntegrable 0 t
    have hiOU : IntervalIntegrable (fun s => (-2*(n : ℝ)) • y s) volume 0 t :=
      (hy.const_smul (-2*(n : ℝ))).intervalIntegrable 0 t
    have hiTilt : IntervalIntegrable (fun s => bakryEmeryGibbsConfigurationTilt n W (y s)) volume 0 t :=
      ((bakryEmeryGibbsConfigurationTilt_continuous W hW).comp hy).intervalIntegrable 0 t
    have hIt : (∫ s in (0 : ℝ)..t, bakryEmeryGibbsConfigurationTilt n W (y s)) =
        (∫ s in (0 : ℝ)..t, bakryEmeryGibbsConfigurationDrift W (y s)) -
          ∫ s in (0 : ℝ)..t, (-2*(n : ℝ)) • y s := by
      rw [← intervalIntegral.integral_sub hiD hiOU]
      exact intervalIntegral.integral_congr (fun s _ =>
        bakryEmeryGibbsConfigurationTilt_eq_drift hn W (hW.differentiable (by norm_num)) (y s))
    have hN : (configurationEuclideanEquiv n).symm (bkWeightedExtension T T.property N t) =
        (ginibreBrownianFullContinuousNoise n B ((n : ℝ)^2) sample).val t -
          ∫ s in (0 : ℝ)..t, bakryEmeryGibbsConfigurationTilt n W (y s) := by
      have htT : t ∈ Icc (0 : ℝ) (T : ℝ) := ⟨ht.1,ht.2.trans (by exact_mod_cast hθ sample)⟩
      have hEval : bkWeightedExtension (T : ℝ) T.property N t = N ⟨t,htT⟩ := by
        unfold bkWeightedExtension
        exact congrArg N (projIcc_of_mem T.property htT)
      rw [hEval]
      simp only [N,bakryEmeryCorrectedCompactDriver,ContinuousMap.coe_mk,bakryEmeryOriginalCompactDriver]
      change (configurationEuclideanEquiv n).symm
        ((configurationEuclideanEquiv n) ((ginibreBrownianFullContinuousNoise n B ((n : ℝ)^2) sample).val t) -
          ∫ s in (0 : ℝ)..t, (configurationEuclideanEquiv n) (bakryEmeryGibbsConfigurationTilt n W (y s))) = _
      rw [map_sub, ContinuousLinearEquiv.symm_apply_apply]
      congr 1
      have he : (configurationEuclideanEquiv n) (∫ s in (0 : ℝ)..t,
          bakryEmeryGibbsConfigurationTilt n W (y s)) =
          ∫ s in (0 : ℝ)..t, (configurationEuclideanEquiv n)
            (bakryEmeryGibbsConfigurationTilt n W (y s)) :=
        ((configurationEuclideanEquiv n).toContinuousLinearMap.intervalIntegral_comp_comm hiTilt).symm
      have he' := congrArg (configurationEuclideanEquiv n).symm he.symm
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using he' 
    rw [hs, hOU, hIOU, hN, hIt]
    abel
  have hId := bakryEmeryGibbsPath_prefix_identification W hW κ hκ hc z T N (θ sample)
    (θ sample).property (by exact_mod_cast hθ sample) y hy.continuousOn hEq
  intro t ht
  have he := hId t ⟨t.property,by exact_mod_cast ht⟩
  simpa only [y,Real.toNNReal_coe,hStopped,min_eq_left ht] using he

#print axioms bakryEmeryGibbsOU_normalized_equation
#print axioms bakryEmeryGibbs_actual_stopped_coupling
end
end GinibrePoincare
