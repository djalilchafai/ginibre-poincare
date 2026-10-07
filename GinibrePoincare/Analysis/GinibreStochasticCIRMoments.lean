module

public import GinibrePoincare.Analysis.GinibreStochasticCIRTransition

@[expose] public section

/-! # Genuine first moments of the autonomous radial transition -/
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem ginibreGaussian_secondMoment (m : ℝ) (v : ℝ≥0) :
    (∫ x : ℝ, x^2 ∂gaussianReal m v) = (v : ℝ) + m^2 := by
  have h := variance_eq_sub (IsGaussian.memLp_two_id (μ := gaussianReal m v))
  simp only [variance_id_gaussianReal, integral_id_gaussianReal, id_eq, Pi.pow_apply] at h
  linarith

 theorem ginibreGaussian_shifted_secondMoment (m : ℝ) (v : ℝ≥0) :
    (∫ x : ℝ, (m+x)^2 ∂gaussianReal 0 v) = (v : ℝ) + m^2 := by
  have hm : (gaussianReal 0 v).map (fun x : ℝ => m+x) = gaussianReal m v := by
    rw [gaussianReal_map_const_add, zero_add]
  rw [← ginibreGaussian_secondMoment m v, ← hm,
    integral_map (by fun_prop) (by fun_prop)]

 theorem ginibreNoncentralRadiusLaw_firstMoment (v : ℝ≥0) (m : ℂ) :
    (∫ r : ℝ, r ∂ginibreNoncentralRadiusLaw v m) = Complex.normSq m + 2*(v : ℝ) := by
  let ν := gaussianReal 0 v
  have hr : MemLp (fun x : ℝ => m.re+x) 2 ν :=
    (memLp_const m.re).add IsGaussian.memLp_two_id
  have hi : MemLp (fun x : ℝ => m.im+x) 2 ν :=
    (memLp_const m.im).add IsGaussian.memLp_two_id
  unfold ginibreNoncentralRadiusLaw ginibrePlanarGaussian
  rw [integral_map (by fun_prop) (by fun_prop),
    integral_map (by fun_prop) (by fun_prop)]
  have he (p : ℝ × ℝ) : Complex.normSq (m + ((p.1 : ℂ)+Complex.I*(p.2 : ℂ))) =
      (m.re+p.1)^2+(m.im+p.2)^2 := by
    simp [Complex.normSq_apply]
    <;> ring
  simp_rw [he]
  rw [integral_add (hr.integrable_sq.comp_fst ν) (hi.integrable_sq.comp_snd ν)]
  have hf : HasLaw Prod.fst ν (ν.prod ν) := measurePreserving_fst.hasLaw
  have hs : HasLaw Prod.snd ν (ν.prod ν) := measurePreserving_snd.hasLaw
  have hrf := hf.integral_comp (f := fun x : ℝ => (m.re+x)^2) (by fun_prop)
  have hif := hs.integral_comp (f := fun x : ℝ => (m.im+x)^2) (by fun_prop)
  change (∫ p : ℝ × ℝ, (m.re+p.1)^2 ∂ν.prod ν) +
    (∫ p : ℝ × ℝ, (m.im+p.2)^2 ∂ν.prod ν) = _
  rw [show (∫ p : ℝ × ℝ, (m.re+p.1)^2 ∂ν.prod ν) = (v : ℝ)+m.re^2 from hrf.trans
      (ginibreGaussian_shifted_secondMoment m.re v),
    show (∫ p : ℝ × ℝ, (m.im+p.2)^2 ∂ν.prod ν) = (v : ℝ)+m.im^2 from hif.trans
      (ginibreGaussian_shifted_secondMoment m.im v)]
  simp [Complex.normSq_apply]
  ring

 theorem ginibreOneParticleCIRTransition_firstMoment (α t : ℝ≥0) (r : ℝ) (hr : 0 ≤ r) :
    (∫ q : ℝ, q ∂ginibreOneParticleCIRTransition α t r) =
      (ginibreOUDecay (2*α) t)^2*r + 2*(ginibreOUVariance (2*α) t : ℝ) := by
  unfold ginibreOneParticleCIRTransition
  rw [ginibreNoncentralRadiusLaw_firstMoment, Complex.normSq_ofReal]
  have h := Real.sq_sqrt hr
  nlinarith [sq_nonneg (ginibreOUDecay (2*α) t)]

end
end GinibrePoincare
