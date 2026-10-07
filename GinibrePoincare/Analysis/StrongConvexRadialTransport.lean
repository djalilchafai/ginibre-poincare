module

public import GinibrePoincare.Analysis.StrongConvexRadialComparison
public import GinibrePoincare.Analysis.StrongConvexTransportMeasure

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

/-- Actual standard-Gaussian transport to the normalized radial Kostlan
measure, with the derived sharp contraction constant. -/
theorem rhoConvex_radial_gaussian_transport (n k : ℕ) (hn : 0 < n)
    (ρ : ℝ) (hρ : 0 < ρ) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V) :
    ∃ T : ℝ → ℝ, ContDiff ℝ 1 T ∧
      (gaussianReal 0 1).map T =
        (volume : Measure ℝ).withDensity (fun r => ENNReal.ofReal
          (radialConfinementProbabilityDensity n k (fun t : ℝ => V (t : ℂ)) r)) ∧
      ∀ x, |deriv T x| ≤ (Real.sqrt ((n : ℝ) * ρ))⁻¹ := by
  let Q := fun r : ℝ => V (r : ℂ)
  have hQ : ContDiff ℝ 2 Q := hV.comp Complex.ofRealCLM.contDiff
  have hi := rhoConvexPotential_radial_density_integrable n k hn ρ hρ hV hrot hc
  let p := radialConfinementProbabilityDensity n k Q
  let ν := (volume : Measure ℝ).withDensity (fun r => ENNReal.ofReal (p r))
  letI : IsProbabilityMeasure ν := radialConfinementProbabilityDensity_isProbability n k Q hQ.continuous hi
  have hp : Continuous p := radialConfinementProbabilityDensity_continuous n k hQ.continuous
  have hpi : Integrable p volume := hi.div_const _
  have hpPos : ∀ r ∈ Ioi (0 : ℝ), 0 < p r := fun r hr =>
    radialConfinementProbabilityDensity_pos n k Q hi hr
  let G := densityCDF p
  have hCDF : cdf ν = G := funext fun x => cdf_withDensity_eq_densityCDF p hp.measurable
    (radialConfinementProbabilityDensity_nonneg n k Q hi) x
  let hm := (radialConfinementProbabilityDensity_CDF_strictMono n k Q hQ.continuous hi).mono Ioi_subset_Ici_self
  let hr := radialConfinementProbabilityDensity_CDF_image n k Q hQ.continuous hi
  let T := cdfQuantileTransport standardGaussianCDF G hm hr
  have hGd : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt G (p r) r := fun r _ => densityCDF_hasDerivAt p hp hpi r
  have hqd := increasingCDFQuantileOn_contDiffOn_one G p (Ioi 0) hm hr hGd
    (fun r hr => (hpPos r hr).ne') hp.continuousOn
  have hFc : ContDiff ℝ 1 standardGaussianCDF := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun x => (standardGaussianCDF_hasDerivAt x).differentiableAt, ?_⟩
    have he : deriv standardGaussianCDF = gaussianPDFReal 0 1 := funext fun x =>
      (standardGaussianCDF_hasDerivAt x).deriv
    rw [he]
    unfold gaussianPDFReal
    fun_prop
  have hTc : ContDiff ℝ 1 T := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    have hx : standardGaussianCDF x ∈ Ioo (0 : ℝ) 1 :=
      standardGaussianCDF_image ▸ mem_image_of_mem standardGaussianCDF (mem_univ x)
    exact (hqd.contDiffAt (isOpen_Ioo.mem_nhds hx)).comp x hFc.contDiffAt
  have hTd (x : ℝ) : HasDerivAt T ((p (T x))⁻¹ * gaussianPDFReal 0 1 x) x :=
    cdfQuantileTransport_hasDerivAt standardGaussianCDF (gaussianPDFReal 0 1) G p
      standardGaussianCDF_hasDerivAt standardGaussianCDF_image hm hr hGd
      (fun r hr => (hpPos r hr).ne') x
  have hm' : StrictMonoOn (cdf ν) (Ioi 0) := hCDF.symm ▸ hm
  have hr' : cdf ν '' Ioi 0 = Ioo 0 1 := hCDF.symm ▸ hr
  have hTeq : cdfQuantileTransport (cdf (gaussianReal 0 1)) (cdf ν) hm' hr' = T := by
    exact congrArg (fun q : ℝ → ℝ => q ∘ standardGaussianCDF)
      (increasingCDFQuantileOn_congr (cdf ν) G (Ioi 0) hm' hr' hm hr hCDF)
  have hzero : ∀ y, y ≤ 0 → cdf ν y = 0 := by
    intro y hy
    rw [hCDF]
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Iic] with r hr
    change r ≤ y at hr
    change p r = 0
    exact div_eq_zero_iff.mpr (Or.inl (radialConfinementDensity_zero n k Q (hr.trans hy)))
  have hmap : (gaussianReal 0 1).map T = ν := by
    have ht' : Measurable (cdfQuantileTransport (cdf (gaussianReal 0 1)) (cdf ν) hm' hr') :=
      hTeq.symm ▸ hTc.continuous.measurable
    have hh := cdfQuantileTransport_map (gaussianReal 0 1) ν standardGaussianCDF_strictMono
      standardGaussianCDF_image hm' hr' hzero ht'
    rw [hTeq] at hh
    exact hh
  have hκ : 0 < (n : ℝ) * ρ := mul_pos (Nat.cast_pos.mpr hn) hρ
  have hsqrt : 0 < Real.sqrt ((n : ℝ) * ρ) := Real.sqrt_pos.mpr hκ
  have hb (x : ℝ) : |deriv T x| ≤ (Real.sqrt ((n : ℝ) * ρ))⁻¹ := by
    have h := cdfQuantileTransport_derivative_bound standardGaussianCDF (gaussianPDFReal 0 1) G p
      standardGaussianCDF_strictMono standardGaussianCDF_image hm hr
      (gaussianPDFReal_nonneg 0 1) hpPos (Real.sqrt ((n : ℝ) * ρ)) hsqrt
      (fun u hu => rhoConvex_radial_profile_dominates_gaussian n k hn ρ hρ hV hrot hc u ⟨hu.1.le, hu.2.le⟩) x
    rw [(hTd x).deriv, abs_of_nonneg h.1]
    exact h.2
  exact ⟨T, hTc, hmap, hb⟩

#print axioms rhoConvex_radial_gaussian_transport
end
end GinibrePoincare
