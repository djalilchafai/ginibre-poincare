module

public import GinibrePoincare.Analysis.NonQuadraticWeyl

@[expose] public section

/-! # Radial weighted Bergman reproduction -/
open MeasureTheory
open scoped ContDiff InnerProductSpace
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Finite confinement mass makes the square-root density genuinely L². -/
theorem planarPotentialHalfWeight_memLp (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (hi : Integrable (fun z => Real.exp (-(n : ℝ) * V z)) volume) :
    MemLp (planarPotentialHalfWeight n V) 2 volume := by
  have hc : Continuous (planarPotentialHalfWeight n V) := by
    unfold planarPotentialHalfWeight
    exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (((continuous_const (y := -(n : ℝ))).mul hV).div_const 2))
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2
  convert hi using 1 <;> first | rfl | skip
  funext z
  rw [← Complex.normSq_eq_norm_sq]
  simp only [planarPotentialHalfWeight, Complex.normSq_ofReal]
  rw [← Real.exp_add]
  congr 1
  ring

/-- Every weighted-square-integrable entire function is reproduced at zero
by the actual finite radial confinement, with no compact support assumption. -/
theorem radialPotential_integral_holomorphic (n : ℕ) (V : ℂ → ℝ)
    (hV : Continuous V) (hr : ∀ z, V z = V (‖z‖ : ℂ))
    (hi : Integrable (fun z => Real.exp (-(n : ℝ) * V z)) volume)
    (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (hm : MemLp (fun z => F z * planarPotentialHalfWeight n V z) 2 volume) :
    (∫ z, Real.exp (-(n : ℝ) * V z) • F z) =
      (∫ z, Real.exp (-(n : ℝ) * V z)) • F 0 := by
  have hh := planarPotentialHalfWeight_memLp n V hV hi
  have hip := hm.integrable_mul hh
  have hp (z : ℂ) : (F z * planarPotentialHalfWeight n V z) * planarPotentialHalfWeight n V z =
      Real.exp (-(n : ℝ) * V z) • F z := by
    rw [mul_assoc]
    unfold planarPotentialHalfWeight
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    have he : -(n : ℝ) * V z / 2 + -(n : ℝ) * V z / 2 = -(n : ℝ) * V z := by ring
    rw [he]
    simp [smul_eq_mul, mul_comm]
  change Integrable (fun z => (F z * planarPotentialHalfWeight n V z) * planarPotentialHalfWeight n V z) volume at hip
  simp_rw [hp] at hip
  have hg : Differentiable ℂ (fun z => F (-z)) := hF.comp differentiable_neg
  have he := radial_integral_holomorphic_mean_value_of_integrable
    (fun z => Real.exp (-(n : ℝ) * V z))
    (Real.continuous_exp.comp ((continuous_const (y := -(n : ℝ))).mul hV)) hi
    (fun z => by rw [hr z]) (fun z => F (-z)) hg 0
    (by simpa only [zero_sub, neg_neg] using hip)
  simpa only [zero_sub, neg_neg, neg_zero] using he

/-- Compact radial observables couple to entire functions only through
constant angular degree. This is the concrete Bergman selection rule. -/
theorem radialPotential_compact_holomorphic_pairing (n : ℕ) (V g : ℂ → ℝ)
    (hV : Continuous V) (hrV : ∀ z, V z = V (‖z‖ : ℂ))
    (hg : Continuous g) (hgc : HasCompactSupport g) (hrg : ∀ z, g z = g (‖z‖ : ℂ))
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) :
    (∫ z, (g z * Real.exp (-(n : ℝ) * V z)) • F z) =
      (∫ z, g z * Real.exp (-(n : ℝ) * V z)) • F 0 := by
  have hc : Continuous (fun z => g z * Real.exp (-(n : ℝ) * V z)) :=
    hg.mul (Real.continuous_exp.comp ((continuous_const (y := -(n : ℝ))).mul hV))
  have he := radial_integral_holomorphic_mean_value
    (fun z => g z * Real.exp (-(n : ℝ) * V z)) hc hgc.mul_right
    (fun z => by rw [hrg z, hrV z]) (fun z => F (-z))
    (hF.comp differentiable_neg) 0
  simpa only [zero_sub, neg_neg, neg_zero] using he

/-- A real radial compact test of zero weighted mean is orthogonal to the
actual entire-function kernel. -/
theorem planarWeighted_radial_zeroMean_orthogonal_kernel
    (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V) (hrV : ∀ z, V z = V (‖z‖ : ℂ))
    (g : PlanarCompactTest) (hgReal : ∀ z, (g z).im = 0)
    (hgr : ∀ z, (g z).re = (g (‖z‖ : ℂ)).re)
    (hmean : (∫ z, (g z).re * Real.exp (-(n : ℝ) * V z)) = 0) :
    planarWeightedTestL2 n V hV.continuous g ∈
      (planarWeakDbarKernel n V (hV.of_le (by norm_num)))ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro u hu
  obtain ⟨F, hF, hm, he⟩ :=
    (mem_planarWeakDbarKernel_iff_holomorphic_representative n V hV u).mp hu
  rw [← he]
  have hc : Continuous (fun z => (g z).re) := Complex.continuous_re.comp g.property.1.continuous
  have hgc : HasCompactSupport (fun z => (g z).re) := g.property.2.comp_left Complex.zero_re
  have hint := radialPotential_compact_holomorphic_pairing n V (fun z => (g z).re)
    hV.continuous hrV hc hgc hgr F hF
  rw [hmean, zero_smul] at hint
  have hi : Integrable (fun z => ((g z).re * Real.exp (-(n : ℝ) * V z)) • F z) volume :=
    ((hc.mul (Real.continuous_exp.comp ((continuous_const (y := -(n : ℝ))).mul hV.continuous))).smul hF.continuous).integrable_of_hasCompactSupport hgc.mul_right.smul_right
  have hir := Complex.reCLM.integral_comp_comm hi
  rw [hint, map_zero] at hir
  rw [L2.inner_def]
  calc
    _ = ∫ z, (((g z).re * Real.exp (-(n : ℝ) * V z)) • F z).re := by
      apply integral_congr_ae
      filter_upwards [(planarWeightedTestMap_memLp n V hV.continuous g).coeFn_toLp,
        hm.coeFn_toLp] with z hzG hzF
      change ⟪((planarWeightedTestMap_memLp n V hV.continuous g).toLp _) z,
        (hm.toLp _) z⟫_ℝ = _
      rw [hzG, hzF]
      change ⟪g z * planarPotentialHalfWeight n V z, F z * planarPotentialHalfWeight n V z⟫_ℝ = _
      have hex : Real.exp (-(n : ℝ) * V z / 2) * Real.exp (-(n : ℝ) * V z / 2) =
          Real.exp (-(n : ℝ) * V z) := by
        rw [← Real.exp_add]; congr 1; ring
      simp only [planarWeightedTestMap, planarPotentialHalfWeight, Complex.inner,
        Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.ofReal_re, Complex.ofReal_im, hgReal z, zero_mul, mul_zero,
        sub_zero, add_zero, Complex.real_smul, smul_eq_mul]
      rw [← hex]
      ring
    _ = 0 := hir

/-- Unconditional scalar radial Poincaré estimate for zero-mean compact
C² real observables under arbitrary radial subharmonic confinement. -/
theorem rhoSubharmonicPotential_radial_zeroMean_gap
    (n : ℕ) (hn : 0 < n) (V : ℂ → ℝ) (ρ : ℝ) (hρpos : 0 < ρ)
    (hV : ContDiff ℝ 2 V) (hρ : IsRhoSubharmonicPotential ρ V)
    (hrV : ∀ z, V z = V (‖z‖ : ℂ)) (g : PlanarCompactTest)
    (hgReal : ∀ z, (g z).im = 0) (hgr : ∀ z, (g z).re = (g (‖z‖ : ℂ)).re)
    (hmean : (∫ z, (g z).re * Real.exp (-(n : ℝ) * V z)) = 0) :
    (∫ z, Complex.normSq (g z) * Real.exp (-(n : ℝ) * V z)) ≤
      (2 / ((n : ℝ) * ρ)) * ∫ z, Complex.normSq (planarDbar g z) * Real.exp (-(n : ℝ) * V z) := by
  rw [← planarWeightedTestL2_norm_sq n V hV.continuous g,
    ← planarWeightedDbarTestL2_norm_sq n V hV.continuous g]
  exact rhoSubharmonicPotential_weak_dbar_gap n hn V ρ hρpos hV hρ
    (planarWeightedTestL2 n V hV.continuous g) (planarWeightedDbarTestL2 n V hV.continuous g)
    (planarWeighted_radial_zeroMean_orthogonal_kernel n V hV hrV g hgReal hgr hmean)
    (planarWeightedTestL2_weak_derivative n V (hV.of_le (by norm_num)) g)

end
end GinibrePoincare
