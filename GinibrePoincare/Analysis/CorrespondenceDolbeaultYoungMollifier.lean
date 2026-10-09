module
public import GinibrePoincare.Analysis.CorrespondenceDolbeaultYoungMollifierPairing

@[expose] public section
open MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem dolbeaultPiBump_convolution_smooth (n : ℕ) (φ : ContDiffBump (0 : ℂ))
    (f : Configuration n → ℂ) (hf : MemLp f 2 volume) :
    ContDiff ℝ ∞ (piPlanarBump n φ ⋆[lsmul ℝ ℝ, volume] f) :=
  (piPlanarBump_compact n φ).contDiff_convolution_left (lsmul ℝ ℝ)
    (dolbeaultPiBump_contDiff n φ) (hf.locallyIntegrable (by norm_num))

theorem dolbeaultPiBump_convolution_memLp (n : ℕ) (φ : ContDiffBump (0 : ℂ))
    (f : Configuration n → ℂ) (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    MemLp (piPlanarBump n φ ⋆[lsmul ℝ ℝ, volume] f) 2 volume :=
  (dolbeaultPiBump_convolution_smooth n φ f hf).continuous.memLp_of_hasCompactSupport
    ((piPlanarBump_compact n φ).convolution (lsmul ℝ ℝ) hc)

/-- Ordinary strong L² smoothing is represented by actual smooth convolution,
for arbitrary compact L² input, without continuity of its representative. -/
theorem dolbeaultPiBump_convolution_ae (n : ℕ) (φ : ContDiffBump (0 : ℂ))
    (f : Configuration n → ℂ) (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    (piL2BumpAverage n φ (hf.toLp f) : Configuration n → ℂ) =ᵐ[volume]
      piPlanarBump n φ ⋆[lsmul ℝ ℝ, volume] f := by
  have hfi : Integrable f volume := by
    have hI := (hf.locallyIntegrable (by norm_num)).integrableOn_isCompact hc
    exact hI.integrable_of_forall_notMem_eq_zero (fun x hx => image_eq_zero_of_notMem_tsupport hx)
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (piL2BumpAverage n φ (hf.toLp f))).locallyIntegrable (by norm_num))
    ((dolbeaultPiBump_convolution_memLp n φ f hf hc).locallyIntegrable (by norm_num))
  intro θ hθ hθc
  let Θ : Configuration n → ℂ := fun x => (θ x : ℂ)
  have hΘ : Continuous Θ := Complex.continuous_ofReal.comp hθ.continuous
  have hcΘ : HasCompactSupport Θ := hθc.comp_left Complex.ofReal_zero
  have he (a : Configuration n) : (∫ x, (hf.toLp f) (x-a)*Θ x) =
      ∫ x, f (x-a)*Θ x := by
    apply integral_congr_ae
    have h := (eventually_add_right_iff (volume : Measure (Configuration n)) (-a)).mpr hf.coeFn_toLp
    filter_upwards [h] with x hx
    simpa only [sub_eq_add_neg] using congrArg (fun t => t*Θ x) hx
  calc
    _ = ∫ x, (piL2BumpAverage n φ (hf.toLp f)) x*Θ x := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by simp [Θ, Complex.real_smul, mul_comm])
    _ = ∫ a, (piPlanarBump n φ a : ℂ)*(∫ x, (hf.toLp f) (x-a)*Θ x) :=
      dolbeaultPiBump_average_test n φ (hf.toLp f) Θ hΘ hcΘ
    _ = ∫ a, (piPlanarBump n φ a : ℂ)*(∫ x, f (x-a)*Θ x) := by simp_rw [he]
    _ = ∫ x, (piPlanarBump n φ ⋆[lsmul ℝ ℝ, volume] f) x*Θ x :=
      (dolbeaultPiBump_convolution_test n φ f Θ hfi hΘ hcΘ).symm
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by simp [Θ, Complex.real_smul, mul_comm])

theorem dolbeaultPiBump_convolution_tendsto (n : ℕ) (φ : ℕ → ContDiffBump (0 : ℂ))
    (hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0))
    (f : Configuration n → ℂ) (hf : MemLp f 2 volume) (hc : HasCompactSupport f) :
    Tendsto (fun m => (dolbeaultPiBump_convolution_memLp n (φ m) f hf hc).toLp
      (piPlanarBump n (φ m) ⋆[lsmul ℝ ℝ, volume] f)) atTop (𝓝 (hf.toLp f)) := by
  have he (m : ℕ) : (dolbeaultPiBump_convolution_memLp n (φ m) f hf hc).toLp
      (piPlanarBump n (φ m) ⋆[lsmul ℝ ℝ, volume] f) = piL2BumpAverage n (φ m) (hf.toLp f) := by
    apply Lp.ext
    exact (dolbeaultPiBump_convolution_memLp n (φ m) f hf hc).coeFn_toLp.trans
      (dolbeaultPiBump_convolution_ae n (φ m) f hf hc).symm
  simp_rw [he]
  exact piL2BumpAverage_tendsto n φ hφ (hf.toLp f)

#print axioms dolbeaultPiBump_convolution_ae
#print axioms dolbeaultPiBump_convolution_tendsto
end
end GinibrePoincare
