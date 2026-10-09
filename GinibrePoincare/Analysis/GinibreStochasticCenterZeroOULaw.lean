module

public import GinibrePoincare.Analysis.GinibreStochasticCenterZeroGaussian
public import GinibrePoincare.Analysis.GinibreDrivenPathOUProjection

@[expose] public section

/-! Gaussian real center laws of the genuine n-particle original process,
including zero initial center and every positive time. -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def ginibreCenterOURate (n : ℕ) (α : ℝ≥0) : ℝ≥0 := 2*α/n

@[simp] theorem ginibreCenterOURate_coe (n : ℕ) (α : ℝ≥0) :
    (ginibreCenterOURate n α : ℝ)=2*(α : ℝ)/(n : ℝ) := by
  simp [ginibreCenterOURate]

theorem ginibre_center_noise_scaling {n : ℕ} (hn : 0 < n) (α : ℝ≥0) :
    Real.sqrt (2*(α : ℝ)/(n : ℝ)^2) =
      Real.sqrt (ginibreCenterOURate n α : ℝ)*(Real.sqrt (n : ℝ))⁻¹ := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsn : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hnR).ne'
  have ha : (Real.sqrt (2*(α : ℝ)/(n : ℝ)^2))^2 = 2*(α : ℝ)/(n : ℝ)^2 := Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) α.coe_nonneg) (sq_nonneg (n : ℝ)))
  have hb : (Real.sqrt (ginibreCenterOURate n α : ℝ))^2 = (ginibreCenterOURate n α : ℝ) := Real.sq_sqrt (ginibreCenterOURate n α).coe_nonneg
  have hc := Real.sq_sqrt hnR.le
  have hsq : (Real.sqrt (ginibreCenterOURate n α : ℝ)*(Real.sqrt (n : ℝ))⁻¹)^2 =
      2*(α : ℝ)/(n : ℝ)^2 := by
    rw [mul_pow, inv_pow, hb, hc, ginibreCenterOURate_coe]
    field_simp
    <;> ring
  nlinarith [Real.sqrt_nonneg (2*(α : ℝ)/(n : ℝ)^2),
    mul_nonneg (Real.sqrt_nonneg (ginibreCenterOURate n α : ℝ)) (inv_nonneg.mpr (Real.sqrt_nonneg (n : ℝ)))]

theorem ginibreBrownian_center_real_OU
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      (coordinateSum (ginibreBrownianMaximalProcess n α z B t ω)).re =
        ginibreBrownianOU (ginibreNormalizedCenterBrownian n 0 B)
          (ginibreCenterOURate n α) (Real.sqrt (ginibreCenterOURate n α : ℝ))
          (coordinateSum z).re t ω := by
  filter_upwards [ginibreBrownian_center_OU_factorization hn α z hz B P hB hind,
    ginibreBrownianFullContinuousNoise_ae n B P hB α] with ω hcenter hnoise
  let N := ginibreContinuousNoiseCenter n (ginibreBrownianFullContinuousNoise n B α ω)
  have he : (fun s : ℝ => Complex.reCLM (N s)) =
      ginibreBrownianNoise (ginibreNormalizedCenterBrownian n 0 B)
        (Real.sqrt (ginibreCenterOURate n α : ℝ)) ω := by
    funext s
    change (coordinateSumCLM n ((ginibreBrownianFullContinuousNoise n B α ω).val s)).re = _
    rw [coordinateSumCLM_apply, hnoise s]
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hns : Real.sqrt (n : ℝ)/(n : ℝ) = (Real.sqrt (n : ℝ))⁻¹ := by
      have hs := (Real.sqrt_pos.mpr hnR).ne'
      field_simp
      nlinarith [Real.sq_sqrt hnR.le]
    simp [hns, coordinateSum, ginibreConfigurationBrownianNoise, ginibreBrownianNoise,
      ginibreNormalizedCenterBrownian,← Finset.mul_sum, ginibre_center_noise_scaling hn α,
      mul_assoc]
  intro t
  rw [hcenter t]
  have hh := drivenOUPath_continuousLinearMap Complex.reCLM (2*(α : ℝ)/(n : ℝ))
    (coordinateSum z) N N.continuous (t : ℝ)
  rw [he] at hh
  simpa [ginibreCenterOUValue, N, ginibreBrownianOU, ginibreCenterOURate_coe, Complex.reCLM] using hh

theorem ginibreBrownian_center_imag_OU
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      (coordinateSum (ginibreBrownianMaximalProcess n α z B t ω)).im =
        ginibreBrownianOU (ginibreNormalizedCenterBrownian n 1 B)
          (ginibreCenterOURate n α) (Real.sqrt (ginibreCenterOURate n α : ℝ))
          (coordinateSum z).im t ω := by
  filter_upwards [ginibreBrownian_center_OU_factorization hn α z hz B P hB hind,
    ginibreBrownianFullContinuousNoise_ae n B P hB α] with ω hcenter hnoise
  let N := ginibreContinuousNoiseCenter n (ginibreBrownianFullContinuousNoise n B α ω)
  have he : (fun s : ℝ => Complex.imCLM (N s)) =
      ginibreBrownianNoise (ginibreNormalizedCenterBrownian n 1 B)
        (Real.sqrt (ginibreCenterOURate n α : ℝ)) ω := by
    funext s
    change (coordinateSumCLM n ((ginibreBrownianFullContinuousNoise n B α ω).val s)).im = _
    rw [coordinateSumCLM_apply, hnoise s]
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hns : Real.sqrt (n : ℝ)/(n : ℝ) = (Real.sqrt (n : ℝ))⁻¹ := by
      have hs := (Real.sqrt_pos.mpr hnR).ne'
      field_simp
      nlinarith [Real.sq_sqrt hnR.le]
    simp [hns, coordinateSum, ginibreConfigurationBrownianNoise, ginibreBrownianNoise,
      ginibreNormalizedCenterBrownian,← Finset.mul_sum, ginibre_center_noise_scaling hn α,
      mul_assoc]
  intro t
  rw [hcenter t]
  have hh := drivenOUPath_continuousLinearMap Complex.imCLM (2*(α : ℝ)/(n : ℝ))
    (coordinateSum z) N N.continuous (t : ℝ)
  rw [he] at hh
  simpa [ginibreCenterOUValue, N, ginibreBrownianOU, ginibreCenterOURate_coe, Complex.imCLM] using hh

#print axioms ginibreBrownian_center_real_OU
#print axioms ginibreBrownian_center_imag_OU
end
end GinibrePoincare
