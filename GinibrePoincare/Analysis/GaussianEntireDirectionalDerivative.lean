module

public import GinibrePoincare.Analysis.GaussianEntireParameterIntegral

@[expose] public section

open MeasureTheory
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def gaussianCircleDerivativeKernel (t : ℝ) : ℂ :=
  circleMap 0 1 t * Complex.I * (circleMap 0 1 t ^ 2)⁻¹

theorem continuous_gaussianCircleDerivativeKernel : Continuous gaussianCircleDerivativeKernel := by
  have hi : Continuous (fun t : ℝ => (circleMap 0 1 t)⁻¹) := by
    simpa using continuous_circleMap_inv (z := 0) (w := 0)
      (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1))
  unfold gaussianCircleDerivativeKernel
  have hh := ((continuous_circleMap 0 1).mul
    (continuous_const : Continuous (fun _ : ℝ => Complex.I))).mul (hi.pow 2)
  convert hh using 1
  funext t
  simp only [Pi.mul_apply, Pi.pow_apply, inv_pow]

/-- Directional complex derivatives of arbitrary multivariate entire
functions are themselves entire. -/
theorem gaussian_entire_directional_fderiv_differentiable {n : ℕ}
    {f : Configuration n → ℂ} (hf : Differentiable ℂ f) (v : Configuration n) :
    Differentiable ℂ (fun z => fderiv ℂ f z v) := by
  let A : Configuration n → ℝ → Configuration n := fun z t => z + circleMap 0 1 t • v
  have hA : Continuous (fun p : Configuration n × ℝ => A p.1 p.2) := by
    change Continuous (fun p : Configuration n × ℝ => p.1 + circleMap 0 1 p.2 • v)
    exact continuous_fst.add (((continuous_circleMap 0 1).comp continuous_snd).smul
      (continuous_const : Continuous (fun _ : Configuration n × ℝ => v)))
  let F : Configuration n → ℝ → ℂ := fun z t => gaussianCircleDerivativeKernel t * f (A z t)
  let F' : Configuration n → ℝ → Configuration n →L[ℂ] ℂ :=
    fun z t => gaussianCircleDerivativeKernel t • fderiv ℂ f (A z t)
  have hF : Continuous ↿F :=
    (continuous_gaussianCircleDerivativeKernel.comp continuous_snd).mul (hf.continuous.comp hA)
  have hF' : Continuous ↿F' :=
    (continuous_gaussianCircleDerivativeKernel.comp continuous_snd).smul
      ((gaussian_entire_contDiff_complex_one hf).continuous_fderiv (by norm_num) |>.comp hA)
  have hd : ∀ z t, HasFDerivAt (fun w => F w t) (F' z t) z := by
    intro z t
    have h := ((hf (A z t)).hasFDerivAt.comp z
      ((hasFDerivAt_id z).add_const (circleMap 0 1 t • v))).const_mul
        (gaussianCircleDerivativeKernel t)
    simpa only [F, F', A, Function.comp_def, ContinuousLinearMap.comp_id, id_eq] using h
  have hI := gaussian_entire_parameter_intervalIntegral F F' hF hF' hd 0 (2 * Real.pi)
  have hrep : ∀ z, fderiv ℂ f z v =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ * ∫ t in 0..2 * Real.pi, F z t := by
    intro z
    let G : ℂ → ℂ := fun w => f (z + w • v)
    have hG : Differentiable ℂ G := hf.comp
      ((differentiable_const z).add (differentiable_id.smul_const v))
    have hcurve : HasDerivAt (fun w : ℂ => z + w • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add z
    have hff : HasFDerivAt f (fderiv ℂ f z) ((fun w : ℂ => z + w • v) 0) := by
      simpa using (hf z).hasFDerivAt
    have hderiv : deriv G 0 = fderiv ℂ f z v := (hff.comp_hasDerivAt 0 hcurve).deriv
    have hc := Complex.cderiv_eq_deriv (z := 0) (U := Set.univ) (f := G) isOpen_univ
      hG.differentiableOn (by norm_num : (0 : ℝ) < 1) (Set.subset_univ _)
    rw [← hderiv, ← hc, Complex.cderiv, circleIntegral]
    simp only [sub_zero, deriv_circleMap, smul_eq_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp [F, A, G, gaussianCircleDerivativeKernel]
    ring
  have htarget : (fun z => fderiv ℂ f z v) =
      fun z => (2 * Real.pi * Complex.I : ℂ)⁻¹ * ∫ t in 0..2 * Real.pi, F z t :=
    funext hrep
  rw [htarget]
  exact (differentiable_const _).mul hI

#print axioms gaussian_entire_directional_fderiv_differentiable

end
end GinibrePoincare
