module
public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryLocalDolbeaultConfiguration
public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryCauchyGreenHomotopy

@[expose] public section
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem parametricCauchyGreen_source_derivative_compact (a : P → ℂ → ℂ)
    (k : Set ℂ) (hk : IsCompact k) (hs : ∀ p z, z ∉ k → a p z = 0)
    (p : P) (b : P × ℂ) :
    HasCompactSupport (fun z => fderiv ℝ (Function.uncurry a) (p,z) b) := by
  apply HasCompactSupport.of_support_subset_isCompact hk
  intro z hz
  by_contra hzk
  have hopen : IsOpen ((univ : Set P) ×ˢ kᶜ) := isOpen_univ.prod hk.isClosed.isOpen_compl
  have he : Function.uncurry a =ᶠ[𝓝 (p,z)] (fun _ => (0 : ℂ)) := by
    filter_upwards [hopen.mem_nhds ⟨mem_univ _,hzk⟩] with q hq
    exact hs q.1 q.2 hq.2
  apply hz
  change (fderiv ℝ (Function.uncurry a) (p,z)) b = 0
  rw [he.fderiv_eq (𝕜 := ℝ)]
  simp

theorem parametricCauchyGreenPotential_transverse_dbar_integral (a : P → ℂ → ℂ)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) (k : Set ℂ) (hk : IsCompact k)
    (hs : ∀ p z, z ∉ k → a p z = 0) (v w : P) (q : P × ℂ) :
    finiteComplexDbar (v,0) (w,0) (parametricCauchyGreenPotential a) q =
      ∫ y : ℂ, cauchyGreenKernel y *
        finiteComplexDbar (v,0) (w,0) (Function.uncurry a) (q.1,q.2-y) := by
  have hi (b : P × ℂ) : Integrable (fun y : ℂ => cauchyGreenKernel y *
      fderiv ℝ (Function.uncurry a) (q.1,q.2-y) b) volume := by
    have hd : Continuous (fun z : ℂ => fderiv ℝ (Function.uncurry a) (q.1,z) b) :=
      ((ha.continuous_fderiv (by simp)).comp
        (continuous_const.prodMk continuous_id)).clm_apply continuous_const
    have hc := parametricCauchyGreen_source_derivative_compact a k hk hs q.1 b
    exact (hc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℂ)
      cauchyGreenKernel_locallyIntegrable hd q.2).integrable
  simp only [finiteComplexDbar]
  rw [parametricCauchyGreenPotential_directional_derivative a ha k hk hs q (v,0),
    parametricCauchyGreenPotential_directional_derivative a ha k hk hs q (w,0)]
  have he : (fun y : ℂ => cauchyGreenKernel y * ((1/2 : ℂ)*
      (fderiv ℝ (Function.uncurry a) (q.1,q.2-y) (v,0) +
        Complex.I*fderiv ℝ (Function.uncurry a) (q.1,q.2-y) (w,0)))) =
      (fun y : ℂ => (1/2 : ℂ)*(cauchyGreenKernel y *
        fderiv ℝ (Function.uncurry a) (q.1,q.2-y) (v,0) +
        Complex.I*(cauchyGreenKernel y *
          fderiv ℝ (Function.uncurry a) (q.1,q.2-y) (w,0)))) := by
    funext y
    ring
  rw [he,integral_const_mul,integral_add (hi (v,0)) ((hi (w,0)).const_mul Complex.I),
    integral_const_mul]

/-- The literal transverse boundary correction for a smooth closed form.
Closedness is imposed only where the solved-coordinate cutoff is supported. -/
theorem parametricCauchyGreen_cutoff_residual (χ : ℂ → ℂ) (a b : P → ℂ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (hb : ContDiff ℝ ∞ (Function.uncurry b)) (v w : P) (q : P × ℂ)
    (hclosed : ∀ z ∈ tsupport χ,
      finiteComplexDbar (v,0) (w,0) (Function.uncurry a) (q.1,z) =
        planarDbar (b q.1) z) :
    finiteComplexDbar (v,0) (w,0) (localizedCauchyGreenPotential χ a) q =
      χ q.2 * b q.1 q.2 -
        cauchyGreenPotential (fun z => planarDbar χ z * b q.1 z) q.2 := by
  let A : P → ℂ → ℂ := fun p z => χ z * a p z
  have hA : ContDiff ℝ ∞ (Function.uncurry A) := (hχ.comp contDiff_snd).mul ha
  have hs : ∀ p z, z ∉ tsupport χ → A p z = 0 := by
    intro p z hz
    simp only [A,image_eq_zero_of_notMem_tsupport hz,zero_mul]
  have hd (z : ℂ) (d : P) : fderiv ℝ (Function.uncurry A) (q.1,z) (d,0) =
      χ z * fderiv ℝ (Function.uncurry a) (q.1,z) (d,0) := by
    have hx := (hχ.differentiable (by simp) z).hasFDerivAt.comp (q.1,z)
      (ContinuousLinearMap.snd ℝ P ℂ).hasFDerivAt
    have hm := hx.mul (ha.differentiable (by simp) (q.1,z)).hasFDerivAt
    have hm' : HasFDerivAt (Function.uncurry A)
        (χ z • fderiv ℝ (Function.uncurry a) (q.1,z) +
          a q.1 z • ((fderiv ℝ χ z).comp (ContinuousLinearMap.snd ℝ P ℂ))) (q.1,z) := by
      simpa only [A,Function.uncurry,Function.comp_def,Pi.mul_apply,
        ContinuousLinearMap.coe_snd] using! hm
    rw [hm'.fderiv]
    simp
  have hder (z : ℂ) : finiteComplexDbar (v,0) (w,0) (Function.uncurry A) (q.1,z) =
      χ z * planarDbar (b q.1) z := by
    by_cases hz : z ∈ tsupport χ
    · have he := hclosed z hz
      simp only [finiteComplexDbar,hd]
      simp only [finiteComplexDbar] at he
      linear_combination χ z * he
    · simp only [finiteComplexDbar,hd,image_eq_zero_of_notMem_tsupport hz,zero_mul,mul_zero,add_zero]
  change finiteComplexDbar (v,0) (w,0) (parametricCauchyGreenPotential A) q = _
  rw [parametricCauchyGreenPotential_transverse_dbar_integral A hA (tsupport χ) hc hs v w q]
  simp_rw [hder]
  have hbs : ContDiff ℝ ∞ (b q.1) := hb.comp (contDiff_const.prodMk contDiff_id)
  exact cauchyGreen_cutoff_homotopy χ (b q.1) hχ hc hbs q.2

#print axioms parametricCauchyGreen_source_derivative_compact
#print axioms parametricCauchyGreenPotential_transverse_dbar_integral
#print axioms parametricCauchyGreen_cutoff_residual
end
end GinibrePoincare
