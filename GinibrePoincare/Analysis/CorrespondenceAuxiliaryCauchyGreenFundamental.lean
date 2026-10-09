module
public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryCauchyGreenIBP
public import GinibrePoincare.Analysis.CorrespondenceLogApproximation

@[expose] public section
open MeasureTheory Filter
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem planarDbar_continuous (θ : ℂ → ℂ) (hθ : ContDiff ℝ 1 θ) :
    Continuous (planarDbar θ) := by
  exact continuous_const.mul
    (((hθ.continuous_fderiv (by norm_num)).clm_apply continuous_const).add
      (continuous_const.mul ((hθ.continuous_fderiv (by norm_num)).clm_apply continuous_const)))

theorem planarDbar_compact (θ : ℂ → ℂ) (hc : HasCompactSupport θ) :
    HasCompactSupport (planarDbar θ) := by
  exact ((hc.fderiv_apply ℝ 1).add
    ((hc.fderiv_apply ℝ Complex.I).mul_left (f := fun _ => Complex.I))).mul_left
      (f := fun _ => (1/2 : ℂ))

/-- Literal ordinary-test fundamental solution identity ∂bar(1/(πz))=δ₀. -/
theorem cauchyGreenKernel_fundamental_identity (θ : ℂ → ℂ)
    (hθ : ContDiff ℝ 1 θ) (hc : HasCompactSupport θ) :
    (∫ z : ℂ, cauchyGreenKernel z * planarDbar θ z) = -θ 0 := by
  have hl := cauchyGreenRegularizedKernel_integral_tendsto (planarDbar θ)
    (planarDbar_continuous θ hθ) (planarDbar_compact θ hc)
  have hr := (correspondenceLogKernel_test_limit θ
    (hθ.continuous.integrable_of_hasCompactSupport hc) hθ.continuous.continuousAt).neg
  have he : (fun τ : ℝ => ∫ z : ℂ, cauchyGreenRegularizedKernel τ z * planarDbar θ z)
      =ᶠ[𝓝[>] 0] (fun τ : ℝ => -(∫ z : ℂ, correspondenceLogKernel τ z • θ z)) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    simpa only [correspondenceLogKernel, Complex.real_smul] using
      cauchyGreenRegularizedKernel_test_identity τ hτ θ hθ hc
  exact tendsto_nhds_unique hl (hr.congr' he.symm)

#print axioms planarDbar_continuous
#print axioms planarDbar_compact
#print axioms cauchyGreenKernel_fundamental_identity
end
end GinibrePoincare
