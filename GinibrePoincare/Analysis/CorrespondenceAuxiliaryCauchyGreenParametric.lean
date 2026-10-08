module
public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryCauchyGreenSmoothSolver

@[expose] public section
open MeasureTheory Set Filter
open scoped ContDiff Convolution Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- The actual Cauchy–Green coordinate solver, retaining all remaining
coordinates as parameters. -/
def parametricCauchyGreenPotential (a : P → ℂ → ℂ) (q : P × ℂ) : ℂ :=
  cauchyGreenPotential (a q.1) q.2

theorem parametricCauchyGreenPotential_contDiff (a : P → ℂ → ℂ)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) (k : Set ℂ) (hk : IsCompact k)
    (hs : ∀ p z, z ∉ k → a p z = 0) :
    ContDiff ℝ ∞ (parametricCauchyGreenPotential a) := by
  have h := contDiffOn_convolution_right_with_param (ContinuousLinearMap.mul ℝ ℂ)
    (s := (univ : Set P)) isOpen_univ hk (fun p z _ hz => hs p z hz)
    cauchyGreenKernel_locallyIntegrable
    (show ContDiffOn ℝ ∞ (Function.uncurry a) (univ ×ˢ univ) from ha.contDiffOn)
  simpa only [univ_prod_univ,contDiffOn_univ,parametricCauchyGreenPotential,
    cauchyGreenPotential] using! h

theorem parametricCauchyGreenPotential_last_dbar (a : P → ℂ → ℂ)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) (k : Set ℂ) (hk : IsCompact k)
    (hs : ∀ p z, z ∉ k → a p z = 0) (p : P) (z : ℂ) :
    planarDbar (fun w => parametricCauchyGreenPotential a (p,w)) z = a p z := by
  have hslice : ContDiff ℝ ∞ (a p) := ha.comp
    (contDiff_const.prodMk contDiff_id)
  have hc : HasCompactSupport (a p) := HasCompactSupport.of_support_subset_isCompact hk
    (fun z hz => by by_contra h; exact hz (hs p z h))
  exact cauchyGreenPotential_solves_dbar (a p) hslice hc z

/-- Joint differentiation under the actual Cauchy–Green integral, including
all transverse parameter directions. -/
theorem parametricCauchyGreenPotential_hasFDerivAt (a : P → ℂ → ℂ)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) (k : Set ℂ) (hk : IsCompact k)
    (hs : ∀ p z, z ∉ k → a p z = 0) (q : P × ℂ) :
    HasFDerivAt (parametricCauchyGreenPotential a)
      ((cauchyGreenKernel ⋆[(ContinuousLinearMap.mul ℝ ℂ).precompR (P × ℂ),volume]
        (fun x : ℂ => fderiv ℝ (Function.uncurry a) (q.1,x))) q.2) q := by
  have h := hasFDerivAt_convolution_right_with_param
    (L := ContinuousLinearMap.mul ℝ ℂ) (s := (univ : Set P))
    isOpen_univ hk (fun p z _ hz => hs p z hz) cauchyGreenKernel_locallyIntegrable
    (show ContDiffOn ℝ 1 (Function.uncurry a) (univ ×ˢ univ) from
      (ha.of_le (by simp)).contDiffOn) q (mem_univ _)
  simpa only [parametricCauchyGreenPotential,cauchyGreenPotential] using! h

private theorem parametric_source_fderiv_compact (a : P → ℂ → ℂ)
    (k : Set ℂ) (hk : IsCompact k) (hs : ∀ p z, z ∉ k → a p z = 0) (p : P) :
    HasCompactSupport (fun z : ℂ => fderiv ℝ (Function.uncurry a) (p,z)) := by
  apply HasCompactSupport.of_support_subset_isCompact hk
  intro z hz
  by_contra hzk
  have hopen : IsOpen ((univ : Set P) ×ˢ kᶜ) := isOpen_univ.prod hk.isClosed.isOpen_compl
  have hmem : (p,z) ∈ ((univ : Set P) ×ˢ kᶜ) := ⟨mem_univ _,hzk⟩
  have he : Function.uncurry a =ᶠ[𝓝 (p,z)] (fun _ => (0 : ℂ)) := by
    filter_upwards [hopen.mem_nhds hmem] with q hq
    exact hs q.1 q.2 hq.2
  exact hz (by simpa using! he.fderiv_eq (𝕜 := ℝ))

/-- Literal joint directional derivative formula, available in particular
for the transverse ∂bar directions in a coordinate-by-coordinate homotopy. -/
theorem parametricCauchyGreenPotential_directional_derivative (a : P → ℂ → ℂ)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) (k : Set ℂ) (hk : IsCompact k)
    (hs : ∀ p z, z ∉ k → a p z = 0) (q v : P × ℂ) :
    fderiv ℝ (parametricCauchyGreenPotential a) q v =
      ∫ y : ℂ, cauchyGreenKernel y * fderiv ℝ (Function.uncurry a) (q.1,q.2-y) v := by
  rw [(parametricCauchyGreenPotential_hasFDerivAt a ha k hk hs q).fderiv]
  have hc := parametric_source_fderiv_compact a k hk hs q.1
  have hd : Continuous (fun z : ℂ => fderiv ℝ (Function.uncurry a) (q.1,z)) :=
    (ha.continuous_fderiv (by simp)).comp (continuous_const.prodMk continuous_id)
  have hi := (hc.convolutionExists_right ((ContinuousLinearMap.mul ℝ ℂ).precompR (P × ℂ))
    cauchyGreenKernel_locallyIntegrable hd q.2).integrable
  rw [convolution,ContinuousLinearMap.integral_apply hi v]
  rfl

/-- A coordinate Cauchy–Green solve preserves actual transverse
Cauchy–Riemann equations, the commutation step used in local iteration. -/
theorem parametricCauchyGreenPotential_transverse_CR_at (a : P → ℂ → ℂ)
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) (k : Set ℂ) (hk : IsCompact k)
    (hs : ∀ p z, z ∉ k → a p z = 0) (v w : P) (q : P × ℂ)
    (hCR : ∀ z, fderiv ℝ (Function.uncurry a) (q.1,z) (v,0) +
      Complex.I*fderiv ℝ (Function.uncurry a) (q.1,z) (w,0) = 0) :
    fderiv ℝ (parametricCauchyGreenPotential a) q (v,0) +
      Complex.I*fderiv ℝ (parametricCauchyGreenPotential a) q (w,0) = 0 := by
  have hi (b : P × ℂ) : Integrable (fun y : ℂ => cauchyGreenKernel y *
      fderiv ℝ (Function.uncurry a) (q.1,q.2-y) b) volume := by
    have hc := (parametric_source_fderiv_compact a k hk hs q.1).comp_left
      (g := fun L : P × ℂ →L[ℝ] ℂ => L b) (by simp)
    have hd : Continuous (fun z : ℂ => fderiv ℝ (Function.uncurry a) (q.1,z) b) :=
      ((ha.continuous_fderiv (by simp)).comp
        (continuous_const.prodMk continuous_id)).clm_apply continuous_const
    exact (hc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℂ)
      cauchyGreenKernel_locallyIntegrable hd q.2).integrable
  rw [parametricCauchyGreenPotential_directional_derivative a ha k hk hs q (v,0),
    parametricCauchyGreenPotential_directional_derivative a ha k hk hs q (w,0),
    ← integral_const_mul,← integral_add (hi (v,0)) ((hi (w,0)).const_mul Complex.I)]
  have he : (fun y : ℂ => cauchyGreenKernel y * fderiv ℝ (Function.uncurry a) (q.1,q.2-y) (v,0) +
      Complex.I*(cauchyGreenKernel y*fderiv ℝ (Function.uncurry a) (q.1,q.2-y) (w,0))) = 0 := by
    funext y
    have h := hCR (q.2-y)
    change _ = (0 : ℂ)
    linear_combination cauchyGreenKernel y * h
  rw [he]
  change (∫ _y : ℂ, (0 : ℂ)) = 0
  exact integral_zero ℂ ℂ

#print axioms parametricCauchyGreenPotential_contDiff
#print axioms parametricCauchyGreenPotential_last_dbar
#print axioms parametricCauchyGreenPotential_hasFDerivAt
#print axioms parametricCauchyGreenPotential_directional_derivative
#print axioms parametric_source_fderiv_compact
#print axioms parametricCauchyGreenPotential_transverse_CR_at
end
end GinibrePoincare
