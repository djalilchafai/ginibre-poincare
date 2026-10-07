module

public import GinibrePoincare.Analysis.GinibreStochasticOneParticleRadius

@[expose] public section

/-! # Rotation invariance of the actual independent planar Gaussian noise -/
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 def ginibrePlanarGaussian (v : ℝ≥0) : Measure ℂ :=
  ((gaussianReal 0 v).prod (gaussianReal 0 v)).map
    (fun p : ℝ × ℝ => (p.1 : ℂ) + Complex.I * (p.2 : ℂ))

 instance (v : ℝ≥0) : IsProbabilityMeasure (ginibrePlanarGaussian v) :=
  (by unfold ginibrePlanarGaussian; infer_instance)

 theorem ginibrePlanarGaussian_charFun (v : ℝ≥0) (t : ℂ) :
    charFun (ginibrePlanarGaussian v) t =
      Complex.exp (- (v : ℂ) * (Complex.normSq t : ℂ) / 2) := by
  rw [charFun_apply]
  unfold ginibrePlanarGaussian
  rw [integral_map (by fun_prop) (by fun_prop)]
  have he (p : ℝ × ℝ) :
      Complex.exp ((inner ℝ ((p.1 : ℂ) + Complex.I * (p.2 : ℂ)) t : ℂ) * Complex.I) =
      Complex.exp ((t.re : ℂ) * (p.1 : ℂ) * Complex.I) *
        Complex.exp ((t.im : ℂ) * (p.2 : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    have hir : inner ℝ ((p.1 : ℂ) + Complex.I * (p.2 : ℂ)) t = t.re*p.1+t.im*p.2 := by
      change (t * (starRingEnd ℂ) ((p.1 : ℂ) + Complex.I * (p.2 : ℂ))).re = _
      simp [Complex.mul_re, Complex.mul_im]
      <;> ring
    rw [hir, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_mul]
    ring
  simp_rw [he]
  rw [integral_prod_mul (fun x : ℝ => Complex.exp ((t.re : ℂ) * (x : ℂ) * Complex.I))
    (fun y : ℝ => Complex.exp ((t.im : ℂ) * (y : ℂ) * Complex.I)), ← charFun_apply_real, ← charFun_apply_real,
    charFun_gaussianReal, charFun_gaussianReal, ← Complex.exp_add]
  congr 1
  simp [Complex.normSq_apply, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow]
  ring

 theorem ginibrePlanarGaussian_rotation (v : ℝ≥0) (u : ℂ) (hu : ‖u‖ = 1) :
    (ginibrePlanarGaussian v).map (fun z => u*z) = ginibrePlanarGaussian v := by
  apply Measure.ext_of_charFun
  funext t
  have he (z : ℂ) : inner ℝ (u*z) t = inner ℝ z ((starRingEnd ℂ) u * t) := by
    change (t * (starRingEnd ℂ) (u*z)).re =
      (((starRingEnd ℂ) u * t) * (starRingEnd ℂ) z).re
    rw [map_mul]
    congr 1
    ring
  rw [charFun_apply, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [he]
  rw [← charFun_apply, ginibrePlanarGaussian_charFun, ginibrePlanarGaussian_charFun,
    Complex.normSq_mul]
  have hnu : Complex.normSq ((starRingEnd ℂ) u) = 1 := by
    rw [Complex.normSq_eq_norm_sq]
    simpa [hu]
  rw [hnu, one_mul]

end
end GinibrePoincare
