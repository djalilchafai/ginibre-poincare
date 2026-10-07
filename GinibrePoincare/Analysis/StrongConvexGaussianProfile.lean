module

public import GinibrePoincare.Analysis.StrongConvexQuantileCalculus
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.Topology.ExtendFrom

@[expose] public section

/-! # The actual standard Gaussian cumulative-density profile -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def standardGaussianCDF : ℝ → ℝ := cdf (gaussianReal 0 1)

theorem standardGaussianCDF_eq_densityCDF :
    standardGaussianCDF = densityCDF (gaussianPDFReal 0 1) := by
  have he : ((volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x))) =
      gaussianReal 0 1 := by
    rw [gaussianReal_of_var_ne_zero (0 : ℝ) (one_ne_zero : (1 : NNReal) ≠ 0)]
    rfl
  letI : IsProbabilityMeasure ((volume : Measure ℝ).withDensity
      (fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x))) := by rw [he]; infer_instance
  funext x
  simpa only [he, standardGaussianCDF] using cdf_withDensity_eq_densityCDF (gaussianPDFReal 0 1)
    (by fun_prop) (gaussianPDFReal_nonneg 0 1) x

theorem standardGaussianCDF_hasDerivAt (x : ℝ) :
    HasDerivAt standardGaussianCDF (gaussianPDFReal 0 1 x) x := by
  rw [standardGaussianCDF_eq_densityCDF]
  exact densityCDF_hasDerivAt _ (by unfold gaussianPDFReal; fun_prop)
    (integrable_gaussianPDFReal 0 1) x

theorem standardGaussianCDF_continuous : Continuous standardGaussianCDF :=
  continuous_iff_continuousAt.mpr fun x => (standardGaussianCDF_hasDerivAt x).continuousAt

theorem standardGaussianCDF_strictMono : StrictMono standardGaussianCDF := by
  apply strictMono_of_deriv_pos
  intro x
  rw [(standardGaussianCDF_hasDerivAt x).deriv]
  exact gaussianPDFReal_pos 0 1 x one_ne_zero

theorem standardGaussianCDF_image : standardGaussianCDF '' univ = Ioo 0 1 :=
  strictly_increasing_CDF_image_univ standardGaussianCDF standardGaussianCDF_continuous
    standardGaussianCDF_strictMono (fun x => ⟨cdf_nonneg _ _, cdf_le_one _ _⟩)
    (tendsto_cdf_atBot _) (tendsto_cdf_atTop _)

def standardGaussianDensityProfile : ℝ → ℝ :=
  densityQuantileProfile standardGaussianCDF (gaussianPDFReal 0 1) univ
    (standardGaussianCDF_strictMono.strictMonoOn univ) standardGaussianCDF_image

theorem standardGaussianDensityProfile_pos (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
    0 < standardGaussianDensityProfile u := by
  simp only [standardGaussianDensityProfile, densityQuantileProfile, if_pos hu]
  exact gaussianPDFReal_pos _ _ _ one_ne_zero

theorem standardGaussianPDF_hasDerivAt (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h := (((((hasDerivAt_id x).pow 2).neg).div_const 2).exp).const_mul
    (1 / Real.sqrt (2 * Real.pi))
  convert h using 1
  all_goals try funext y
  all_goals first | rfl | (simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, id_eq, Pi.pow_apply, Pi.neg_apply]; norm_num <;> ring)

theorem standardGaussianDensityProfile_contDiffAt (u : ℝ) (hu : u ∈ Ioo (0 : ℝ) 1) :
    ContDiffAt ℝ 2 standardGaussianDensityProfile u := by
  apply densityQuantileProfile_contDiffAt_two
    standardGaussianCDF (gaussianPDFReal 0 1) univ
    (standardGaussianCDF_strictMono.strictMonoOn univ) standardGaussianCDF_image
    (fun x _ => standardGaussianCDF_hasDerivAt x)
    (fun x _ => (gaussianPDFReal_pos 0 1 x one_ne_zero).ne') _ u hu
  apply ContDiff.contDiffOn
  unfold gaussianPDFReal
  fun_prop

theorem standardGaussianDensityProfile_second_derivative (u : ℝ)
    (hu : u ∈ Ioo (0 : ℝ) 1) :
    deriv (deriv standardGaussianDensityProfile) u =
      -1 / standardGaussianDensityProfile u := by
  let W : ℝ → ℝ := fun x => x ^ 2 / 2
  have hd (x : ℝ) : deriv W x = x := by
    have h := ((hasDerivAt_id x).pow 2).div_const 2
    convert h.deriv using 1 <;> dsimp [W] <;> ring
  have hdd (x : ℝ) : deriv (deriv W) x = 1 := by
    have he : deriv W = id := funext hd
    rw [he]
    exact deriv_id x
  have h := densityQuantileProfile_second_derivative
    standardGaussianCDF (gaussianPDFReal 0 1) W univ
    (standardGaussianCDF_strictMono.strictMonoOn univ) standardGaussianCDF_image
    (fun x _ => standardGaussianCDF_hasDerivAt x)
    (fun x _ => (gaussianPDFReal_pos 0 1 x one_ne_zero).ne')
    (fun x _ => by rw [hd]; exact standardGaussianPDF_hasDerivAt x)
    (fun x _ => by dsimp [W]; fun_prop) u hu
  simpa only [hdd, standardGaussianDensityProfile] using h

theorem increasingCDFQuantileOn_univ_tendsto_atBot (F : ℝ → ℝ)
    (hm : StrictMono F) (hr : F '' univ = Ioo 0 1) :
    Tendsto (increasingCDFQuantileOn F univ (hm.strictMonoOn univ) hr)
      (𝓝[Ioo 0 1] 0) atBot := by
  apply tendsto_atBot.2
  intro b
  have hFb : 0 < F b := (hr ▸ mem_image_of_mem F (mem_univ b)).1
  filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds hFb), self_mem_nhdsWithin] with u hu huI
  have he := increasingCDFQuantileOn_right_inverse F univ (hm.strictMonoOn univ) hr u huI
  by_contra hn
  have h := hm.monotone (le_of_not_ge hn)
  rw [he] at h
  exact (not_le_of_gt hu) h

theorem increasingCDFQuantileOn_univ_tendsto_atTop (F : ℝ → ℝ)
    (hm : StrictMono F) (hr : F '' univ = Ioo 0 1) :
    Tendsto (increasingCDFQuantileOn F univ (hm.strictMonoOn univ) hr)
      (𝓝[Ioo 0 1] 1) atTop := by
  apply tendsto_atTop.2
  intro b
  have hFb : F b < 1 := (hr ▸ mem_image_of_mem F (mem_univ b)).2
  filter_upwards [nhdsWithin_le_nhds (eventually_gt_nhds hFb), self_mem_nhdsWithin] with u hu huI
  have he := increasingCDFQuantileOn_right_inverse F univ (hm.strictMonoOn univ) hr u huI
  by_contra hn
  have h := hm.monotone (le_of_not_ge hn)
  rw [he] at h
  exact (not_le_of_gt hu) h

theorem standardGaussianPDF_tendsto_zero_cocompact :
    Tendsto (gaussianPDFReal 0 1) (cocompact ℝ) (𝓝 0) := by
  have h := (tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
    (by norm_num : (0 : ℝ) < 1 / 2) 0).const_mul (1 / Real.sqrt (2 * Real.pi))
  have he : gaussianPDFReal 0 1 = fun x : ℝ =>
      (1 / Real.sqrt (2 * Real.pi)) * (|x| ^ (0 : ℝ) * Real.exp (-(1 / 2) * x ^ 2)) := by
    funext x
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, Real.rpow_zero, one_mul]
    congr 1
    · simp [one_div]
    · exact congrArg Real.exp (by ring)
  rw [he]
  simpa only [mul_zero] using h


theorem standardGaussianDensityProfile_continuousOn :
    ContinuousOn standardGaussianDensityProfile (Icc 0 1) := by
  let q := increasingCDFQuantileOn standardGaussianCDF univ
    (standardGaussianCDF_strictMono.strictMonoOn univ) standardGaussianCDF_image
  let f := gaussianPDFReal 0 1 ∘ q
  have hleft : Tendsto f (𝓝[Ioo 0 1] 0) (𝓝 0) :=
    (standardGaussianPDF_tendsto_zero_cocompact.mono_left atBot_le_cocompact).comp
      (increasingCDFQuantileOn_univ_tendsto_atBot _ standardGaussianCDF_strictMono
        standardGaussianCDF_image)
  have hright : Tendsto f (𝓝[Ioo 0 1] 1) (𝓝 0) :=
    (standardGaussianPDF_tendsto_zero_cocompact.mono_left atTop_le_cocompact).comp
      (increasingCDFQuantileOn_univ_tendsto_atTop _ standardGaussianCDF_strictMono
        standardGaussianCDF_image)
  have hp : Continuous (gaussianPDFReal 0 1) := by unfold gaussianPDFReal; fun_prop
  have hcont : ContinuousOn f (Ioo 0 1) :=
    hp.comp_continuousOn (increasingCDFQuantileOn_continuousOn _ univ
      (standardGaussianCDF_strictMono.strictMonoOn univ) standardGaussianCDF_image)
  have hclosure : Icc (0 : ℝ) 1 ⊆ closure (Ioo 0 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  have hc : ContinuousOn (extendFrom (Ioo 0 1) f) (Icc 0 1) := by
    apply continuousOn_extendFrom hclosure
    intro x hx
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hx with (rfl | rfl | hx)
    · exact ⟨0, hleft⟩
    · exact ⟨0, hright⟩
    · exact ⟨f x, hcont x hx⟩
  apply hc.congr
  intro x hx
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hx with (rfl | rfl | hx)
  · rw [extendFrom_eq (hclosure (left_mem_Icc.mpr (by norm_num))) hleft]
    simp [standardGaussianDensityProfile, densityQuantileProfile]
  · rw [extendFrom_eq (hclosure (right_mem_Icc.mpr (by norm_num))) hright]
    simp [standardGaussianDensityProfile, densityQuantileProfile]
  · rw [extendFrom_extends hcont x hx]
    simp [standardGaussianDensityProfile, densityQuantileProfile, hx, f, q]


end
end GinibrePoincare
