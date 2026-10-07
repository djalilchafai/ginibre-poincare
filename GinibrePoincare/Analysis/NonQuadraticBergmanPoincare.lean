module

public import GinibrePoincare.Analysis.NonQuadraticBergmanRadial

@[expose] public section

/-! # Centered radial observables in the actual weighted Hilbert space -/
open MeasureTheory
open scoped ContDiff InnerProductSpace
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Exact real Hilbert pairing with an entire weighted function. -/
theorem planarWeightedReal_pairing (n : ℕ) (V g : ℂ → ℝ) (F : ℂ → ℂ)
    (hg : MemLp (fun z => (g z : ℂ) * planarPotentialHalfWeight n V z) 2 volume)
    (hF : MemLp (fun z => F z * planarPotentialHalfWeight n V z) 2 volume) :
    ⟪hg.toLp _, hF.toLp _⟫_ℝ =
      (∫ z, (g z * Real.exp (-(n : ℝ) * V z)) • F z).re := by
  have hp (z : ℂ) : ((g z : ℂ) * planarPotentialHalfWeight n V z) *
      (F z * planarPotentialHalfWeight n V z) =
      (g z * Real.exp (-(n : ℝ) * V z)) • F z := by
    have he : Real.exp (-(n : ℝ) * V z / 2) * Real.exp (-(n : ℝ) * V z / 2) =
        Real.exp (-(n : ℝ) * V z) := by
      rw [← Real.exp_add]; congr 1; ring
    simp only [planarPotentialHalfWeight, Complex.real_smul, smul_eq_mul]
    rw [← he]
    push_cast
    ring
  have hi := hg.integrable_mul hF
  change Integrable (fun z => ((g z : ℂ) * planarPotentialHalfWeight n V z) *
    (F z * planarPotentialHalfWeight n V z)) volume at hi
  simp_rw [hp] at hi
  have hir : (∫ z, (g z * Real.exp (-(n : ℝ) * V z)) • F z).re =
      ∫ z, ((g z * Real.exp (-(n : ℝ) * V z)) • F z).re :=
    (Complex.reCLM.integral_comp_comm hi).symm
  rw [L2.inner_def, hir]
  apply integral_congr_ae
  filter_upwards [hg.coeFn_toLp, hF.coeFn_toLp] with z hzG hzF
  rw [hzG, hzF]
  change ⟪(g z : ℂ) * planarPotentialHalfWeight n V z,
    F z * planarPotentialHalfWeight n V z⟫_ℝ = _
  rw [← hp]
  simp only [Complex.inner, planarPotentialHalfWeight, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero,
    add_zero, neg_zero, Complex.reCLM_apply]
  ring

/-- Radial selection applies to noncompact finite-mass observables as well,
so subtracting the mean does not require a compactness hypothesis. -/
theorem planarWeightedReal_radial_zeroMean_orthogonal_kernel
    (n : ℕ) (V g : ℂ → ℝ) (hV : ContDiff ℝ 2 V)
    (hrV : ∀ z, V z = V (‖z‖ : ℂ)) (hg : Continuous g)
    (hrg : ∀ z, g z = g (‖z‖ : ℂ))
    (hgi : Integrable (fun z => g z * Real.exp (-(n : ℝ) * V z)) volume)
    (hG : MemLp (fun z => (g z : ℂ) * planarPotentialHalfWeight n V z) 2 volume)
    (hmean : (∫ z, g z * Real.exp (-(n : ℝ) * V z)) = 0) :
    hG.toLp _ ∈ (planarWeakDbarKernel n V (hV.of_le (by norm_num)))ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro u hu
  obtain ⟨F, hF, hm, he⟩ :=
    (mem_planarWeakDbarKernel_iff_holomorphic_representative n V hV u).mp hu
  rw [← he, planarWeightedReal_pairing]
  have hi := hG.integrable_mul hm
  have hp (z : ℂ) : ((g z : ℂ) * planarPotentialHalfWeight n V z) *
      (F z * planarPotentialHalfWeight n V z) =
      (g z * Real.exp (-(n : ℝ) * V z)) • F z := by
    have hex : Real.exp (-(n : ℝ) * V z / 2) * Real.exp (-(n : ℝ) * V z / 2) =
        Real.exp (-(n : ℝ) * V z) := by
      rw [← Real.exp_add]; congr 1; ring
    simp only [planarPotentialHalfWeight, Complex.real_smul]
    rw [← hex]
    push_cast
    ring
  change Integrable (fun z => ((g z : ℂ) * planarPotentialHalfWeight n V z) *
    (F z * planarPotentialHalfWeight n V z)) volume at hi
  simp_rw [hp] at hi
  have hh := radial_integral_holomorphic_mean_value_of_integrable
    (fun z => g z * Real.exp (-(n : ℝ) * V z))
    (hg.mul (Real.continuous_exp.comp ((continuous_const (y := -(n : ℝ))).mul hV.continuous)))
    hgi (fun z => by rw [hrg z, hrV z]) (fun z => F (-z))
    (hF.comp differentiable_neg) 0 (by simpa only [zero_sub, neg_neg] using hi)
  simpa only [zero_sub, neg_neg, neg_zero, hmean, zero_smul, Complex.zero_re] using
    congrArg Complex.re hh

/-- Subtracting the actual mean gives a genuine weighted-kernel-orthogonal
vector and hence an unconditional radial Poincaré estimate. -/
theorem rhoSubharmonicPotential_centered_radial_gap
    (n : ℕ) (hn : 0 < n) (V : ℂ → ℝ) (ρ : ℝ) (hρpos : 0 < ρ)
    (hV : ContDiff ℝ 2 V) (hρ : IsRhoSubharmonicPotential ρ V)
    (hrV : ∀ z, V z = V (‖z‖ : ℂ))
    (hi : Integrable (fun z => Real.exp (-(n : ℝ) * V z)) volume)
    (g : PlanarCompactTest) (hgReal : ∀ z, (g z).im = 0)
    (hgr : ∀ z, (g z).re = (g (‖z‖ : ℂ)).re) :
    let hh := planarPotentialHalfWeight_memLp n V hV.continuous hi
    let c := (∫ z, (g z).re * Real.exp (-(n : ℝ) * V z)) /
      (∫ z, Real.exp (-(n : ℝ) * V z))
    ‖planarWeightedTestL2 n V hV.continuous g - c • hh.toLp _‖ ^ 2 ≤
      (2 / ((n : ℝ) * ρ)) *
        ∫ z, Complex.normSq (planarDbar g z) * Real.exp (-(n : ℝ) * V z) := by
  dsimp only
  let hh := planarPotentialHalfWeight_memLp n V hV.continuous hi
  let c := (∫ z, (g z).re * Real.exp (-(n : ℝ) * V z)) /
    (∫ z, Real.exp (-(n : ℝ) * V z))
  have hc : Continuous (fun z => (g z).re) := Complex.continuous_re.comp g.property.1.continuous
  have he (z : ℂ) : ((g z).re : ℂ) = g z := by
    apply Complex.ext
    · rfl
    · simp [hgReal z]
  have hg : MemLp (fun z => ((g z).re : ℂ) * planarPotentialHalfWeight n V z) 2 volume := by
    have hm := planarWeightedTestMap_memLp n V hV.continuous g
    change MemLp (fun z => g z * planarPotentialHalfWeight n V z) 2 volume at hm
    simpa only [he] using hm
  have hG : MemLp (fun z => (((g z).re - c : ℝ) : ℂ) * planarPotentialHalfWeight n V z) 2 volume := by
    convert hg.sub (hh.const_smul c) using 1 <;> first | rfl | skip
    funext z
    simp only [Pi.sub_apply, Pi.smul_apply, Complex.real_smul]
    push_cast
    ring
  let u := planarWeightedTestL2 n V hV.continuous g - c • hh.toLp _
  have hue : hG.toLp _ = u := by
    apply Lp.ext
    filter_upwards [hG.coeFn_toLp, Lp.coeFn_sub (planarWeightedTestL2 n V hV.continuous g) (c • hh.toLp _),
      Lp.coeFn_smul c (hh.toLp _), hh.coeFn_toLp,
      (planarWeightedTestMap_memLp n V hV.continuous g).coeFn_toLp] with z hz hzsub hzsmul hzh hzG
    rw [hz, hzsub]
    simp only [Pi.sub_apply]
    rw [hzsmul]
    simp only [Pi.smul_apply]
    rw [hzh]
    change (((g z).re - c : ℝ) : ℂ) * planarPotentialHalfWeight n V z =
      ((planarWeightedTestMap_memLp n V hV.continuous g).toLp _) z - c • planarPotentialHalfWeight n V z
    rw [hzG]
    change (((g z).re - c : ℝ) : ℂ) * planarPotentialHalfWeight n V z =
      g z * planarPotentialHalfWeight n V z - c • planarPotentialHalfWeight n V z
    rw [← he]
    simp only [Complex.ofReal_re, Complex.real_smul]
    push_cast
    ring
  have hig : Integrable (fun z => (g z).re * Real.exp (-(n : ℝ) * V z)) volume :=
    (hc.mul (Real.continuous_exp.comp ((continuous_const (y := -(n : ℝ))).mul hV.continuous))).integrable_of_hasCompactSupport
      (g.property.2.comp_left Complex.zero_re).mul_right
  have hgi : Integrable (fun z => ((g z).re - c) * Real.exp (-(n : ℝ) * V z)) volume := by
    convert hig.sub (hi.const_mul c) using 1 <;> first | rfl | skip
    funext z
    exact sub_mul _ _ _
  have hmass : (∫ z, Real.exp (-(n : ℝ) * V z)) ≠ 0 := by
    apply ne_of_gt
    exact integral_pos_of_integrable_nonneg_nonzero
      (Real.continuous_exp.comp ((continuous_const (y := -(n : ℝ))).mul hV.continuous)) hi
      (fun z => (Real.exp_pos _).le) (Real.exp_ne_zero (-(n : ℝ) * V 0))
  have hmean : (∫ z, ((g z).re - c) * Real.exp (-(n : ℝ) * V z)) = 0 := by
    simp_rw [sub_mul]
    rw [integral_sub (f := fun z => (g z).re * Real.exp (-(n : ℝ) * V z))
      (g := fun z => c * Real.exp (-(n : ℝ) * V z)) hig (hi.const_mul c), integral_const_mul]
    dsimp only [c]
    rw [div_mul_cancel₀ _ hmass, sub_self]
  have horth : u ∈ (planarWeakDbarKernel n V (hV.of_le (by norm_num)))ᗮ := by
    rw [← hue]
    exact planarWeightedReal_radial_zeroMean_orthogonal_kernel n V _ hV hrV
      (hc.sub continuous_const) (fun z => by change (g z).re - c = (g (‖z‖ : ℂ)).re - c; rw [hgr z]) hgi hG hmean
  have h1 : MemLp (fun z => (1 : ℂ) * planarPotentialHalfWeight n V z) 2 volume := by
    simpa only [one_mul] using hh
  have h1eq : h1.toLp _ = hh.toLp _ := by
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall (fun z => one_mul _)
  have hk : hh.toLp _ ∈ planarWeakDbarKernel n V (hV.of_le (by norm_num)) := by
    rw [← h1eq]
    exact weighted_holomorphic_mem_weak_dbar_kernel n V (hV.of_le (by norm_num)) _
      (differentiable_const 1) h1
  have hpair (φ : PlanarCompactTest) :
      ⟪u, planarWeightedAdjointTestL2 n V (hV.of_le (by norm_num)) φ⟫_ℝ =
        ⟪planarWeightedDbarTestL2 n V hV.continuous g, planarWeightedTestL2 n V hV.continuous φ⟫_ℝ := by
    have hz := (mem_planarWeakDbarKernel_iff n V (hV.of_le (by norm_num)) _).mp hk φ
    change ⟪planarWeightedTestL2 n V hV.continuous g - c • hh.toLp _, _⟫_ℝ = _
    rw [inner_sub_left, real_inner_smul_left, hz, mul_zero, sub_zero]
    exact planarWeightedTestL2_weak_derivative n V (hV.of_le (by norm_num)) g φ
  have hgap := rhoSubharmonicPotential_weak_dbar_gap n hn V ρ hρpos hV hρ u
    (planarWeightedDbarTestL2 n V hV.continuous g) horth hpair
  rwa [planarWeightedDbarTestL2_norm_sq] at hgap

/-- Centering in the weighted Hilbert space is exactly the literal centered
second-moment integral. -/
theorem planarWeighted_centered_norm_sq
    (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) (g : PlanarCompactTest)
    (hgReal : ∀ z, (g z).im = 0) (c : ℝ)
    (hh : MemLp (planarPotentialHalfWeight n V) 2 volume) :
    ‖planarWeightedTestL2 n V hV g - c • hh.toLp _‖ ^ 2 =
      ∫ z, ((g z).re - c) ^ 2 * Real.exp (-(n : ℝ) * V z) := by
  rw [← integral_norm_sq_eq_L2_norm_sq volume]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (planarWeightedTestL2 n V hV g) (c • hh.toLp _),
    Lp.coeFn_smul c (hh.toLp _), hh.coeFn_toLp,
    (planarWeightedTestMap_memLp n V hV g).coeFn_toLp] with z hzsub hzsmul hzh hzG
  rw [hzsub]
  simp only [Pi.sub_apply]
  rw [hzsmul]
  simp only [Pi.smul_apply]
  rw [hzh]
  change ‖((planarWeightedTestMap_memLp n V hV g).toLp _) z - c • planarPotentialHalfWeight n V z‖ ^ 2 = _
  rw [hzG]
  change ‖g z * planarPotentialHalfWeight n V z - c • planarPotentialHalfWeight n V z‖ ^ 2 = _
  have he : g z = ((g z).re : ℂ) := by
    apply Complex.ext
    · rfl
    · simp [hgReal z]
  rw [he]
  simp only [Complex.ofReal_re]
  have hp : ((g z).re : ℂ) * planarPotentialHalfWeight n V z - c • planarPotentialHalfWeight n V z =
      (((g z).re - c : ℝ) : ℂ) * planarPotentialHalfWeight n V z := by
    simp only [Complex.real_smul]
    push_cast
    ring
  rw [hp, ← Complex.normSq_eq_norm_sq, Complex.normSq_mul]
  simp only [planarPotentialHalfWeight, Complex.normSq_ofReal]
  rw [← Real.exp_add]
  have hr : -(n : ℝ) * V z / 2 + -(n : ℝ) * V z / 2 = -(n : ℝ) * V z := by ring
  rw [hr]
  ring

/-- Literal centered-integral radial Poincaré inequality for arbitrary
nonquadratic finite-mass subharmonic confinement. -/
theorem rhoSubharmonicPotential_radial_centered_integral_gap
    (n : ℕ) (hn : 0 < n) (V : ℂ → ℝ) (ρ : ℝ) (hρpos : 0 < ρ)
    (hV : ContDiff ℝ 2 V) (hρ : IsRhoSubharmonicPotential ρ V)
    (hrV : ∀ z, V z = V (‖z‖ : ℂ))
    (hi : Integrable (fun z => Real.exp (-(n : ℝ) * V z)) volume)
    (g : PlanarCompactTest) (hgReal : ∀ z, (g z).im = 0)
    (hgr : ∀ z, (g z).re = (g (‖z‖ : ℂ)).re) :
    let c := (∫ z, (g z).re * Real.exp (-(n : ℝ) * V z)) /
      (∫ z, Real.exp (-(n : ℝ) * V z))
    (∫ z, ((g z).re - c) ^ 2 * Real.exp (-(n : ℝ) * V z)) ≤
      (2 / ((n : ℝ) * ρ)) *
        ∫ z, Complex.normSq (planarDbar g z) * Real.exp (-(n : ℝ) * V z) := by
  have he := rhoSubharmonicPotential_centered_radial_gap n hn V ρ hρpos hV hρ hrV hi g hgReal hgr
  dsimp only at he ⊢
  rwa [planarWeighted_centered_norm_sq n V hV.continuous g hgReal] at he

/-- For real observables, the Wirtinger energy is one quarter of the
ordinary planar gradient energy. -/
theorem planarDbar_real_normSq (f : ℂ → ℂ) (hf : Differentiable ℝ f)
    (hreal : ∀ z, (f z).im = 0) (z : ℂ) :
    Complex.normSq (planarDbar f z) = (1 / 4 : ℝ) *
      (planarDerivative 1 (fun w => (f w).re) z ^ 2 +
        planarDerivative Complex.I (fun w => (f w).re) z ^ 2) := by
  rw [← planarDbarOfParts_eq f hf z]
  have hi : (fun w => (f w).im) = (fun _ => (0 : ℝ)) := funext hreal
  simp only [hi, planarDbarOfParts, planarDerivative, fderiv_const_apply,
    ContinuousLinearMap.zero_apply, sub_zero, add_zero, Complex.normSq_apply]
  ring

/-- The arbitrary nonquadratic scalar radial Poincaré bound in ordinary
planar-gradient normalization, at the paper's exact constant 1/(2nρ). -/
theorem rhoSubharmonicPotential_radial_centered_gradient_gap
    (n : ℕ) (hn : 0 < n) (V : ℂ → ℝ) (ρ : ℝ) (hρpos : 0 < ρ)
    (hV : ContDiff ℝ 2 V) (hρ : IsRhoSubharmonicPotential ρ V)
    (hrV : ∀ z, V z = V (‖z‖ : ℂ))
    (hi : Integrable (fun z => Real.exp (-(n : ℝ) * V z)) volume)
    (g : PlanarCompactTest) (hgReal : ∀ z, (g z).im = 0)
    (hgr : ∀ z, (g z).re = (g (‖z‖ : ℂ)).re) :
    let c := (∫ z, (g z).re * Real.exp (-(n : ℝ) * V z)) /
      (∫ z, Real.exp (-(n : ℝ) * V z))
    (∫ z, ((g z).re - c) ^ 2 * Real.exp (-(n : ℝ) * V z)) ≤
      (1 / (2 * (n : ℝ) * ρ)) * ∫ z,
        (planarDerivative 1 (fun w => (g w).re) z ^ 2 +
          planarDerivative Complex.I (fun w => (g w).re) z ^ 2) * Real.exp (-(n : ℝ) * V z) := by
  have he := rhoSubharmonicPotential_radial_centered_integral_gap n hn V ρ hρpos hV hρ hrV hi g hgReal hgr
  dsimp only at he ⊢
  simp_rw [planarDbar_real_normSq g (g.property.1.differentiable (by norm_num)) hgReal, mul_assoc] at he
  rw [integral_const_mul] at he
  have hc : 2 / ((n : ℝ) * ρ) * (1 / 4 : ℝ) = 1 / (2 * (n : ℝ) * ρ) := by
    field_simp
    ring
  rwa [← mul_assoc, hc] at he

end
end GinibrePoincare
