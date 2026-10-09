module
public import GinibrePoincare.Analysis.CorrespondenceLogLimit

@[expose] public section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem planarPartial_continuous (θ : ℂ → ℂ) (hθ : ContDiff ℝ 1 θ) :
    Continuous (planarPartial θ) := by
  exact continuous_const.mul
    (((hθ.continuous_fderiv (by norm_num)).clm_apply continuous_const).sub
      (continuous_const.mul ((hθ.continuous_fderiv (by norm_num)).clm_apply continuous_const)))

theorem planarPartial_compact (θ : ℂ → ℂ) (hc : HasCompactSupport θ) :
    HasCompactSupport (planarPartial θ) := by
  exact ((hc.fderiv_apply ℝ 1).sub
    ((hc.fderiv_apply ℝ Complex.I).mul_left (f := fun _ => Complex.I))).mul_left
      (f := fun _ => (1/2 : ℂ))

/-- Actual distributional holomorphic derivative of the locally integrable logarithm. -/
theorem correspondenceLogPotential_weak_partial (θ : ℂ → ℂ)
    (hθ : ContDiff ℝ 1 θ) (hc : HasCompactSupport θ) :
    (∫ z : ℂ, (correspondenceLogPotential z : ℂ)*planarPartial θ z) =
      -(Real.pi/2 : ℂ)*(∫ z : ℂ, cauchyGreenKernel z*θ z) := by
  have hl := correspondenceLogRegularized_integral_tendsto (planarPartial θ)
    (planarPartial_continuous θ hθ) (planarPartial_compact θ hc)
  have hr := (cauchyGreenRegularizedKernel_integral_tendsto θ hθ.continuous hc).const_mul
    (-(Real.pi/2 : ℂ))
  have he : (fun τ : ℝ => ∫ z : ℂ, (correspondenceLogRegularized τ z : ℂ)*planarPartial θ z)
      =ᶠ[𝓝[>] 0] (fun τ : ℝ => -(Real.pi/2 : ℂ)*
        (∫ z : ℂ, cauchyGreenRegularizedKernel τ z*θ z)) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hf : ContDiff ℝ 1 (fun z => (correspondenceLogRegularized τ z : ℂ)) := by
      simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
        ((Complex.ofRealCLM.contDiff.comp (correspondenceLogRegularized_contDiff τ hτ)).of_le (by simp) : ContDiff ℝ 1 _)
    rw [planarPartial_compact_integrationByParts _ _
      hf hθ hc]
    simp_rw [correspondenceLogRegularized_partial τ hτ, mul_assoc]
    rw [integral_const_mul]
    ring
  exact tendsto_nhds_unique hl (hr.congr' he.symm)

#print axioms correspondenceLogPotential_weak_partial
end
end GinibrePoincare
