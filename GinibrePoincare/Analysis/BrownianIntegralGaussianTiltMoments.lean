module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.HasLaw

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

def gaussianExponentialTilt (h : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  Real.exp (h*x-h^2*(v : ℝ)/2)

theorem gaussianExponentialTilt_integrable (h : ℝ) (v : ℝ≥0) :
    Integrable (gaussianExponentialTilt h v) (gaussianReal 0 v) := by
  have he : gaussianExponentialTilt h v =
      (fun x => Real.exp (-h^2*(v : ℝ)/2)*Real.exp (h*x)) := by
    funext x
    rw [gaussianExponentialTilt,← Real.exp_add]
    congr 1
    ring
  rw [he]
  exact (integrable_exp_mul_gaussianReal h).const_mul _

theorem gaussianExponentialTilt_exponential_moment (h p : ℝ) (v : ℝ≥0) :
    (∫ x, Real.exp (p*(h*x-h^2*(v : ℝ)/2)) ∂gaussianReal 0 v) =
      Real.exp ((p^2-p)*h^2*(v : ℝ)/2) := by
  have he (x : ℝ) : Real.exp (p*(h*x-h^2*(v : ℝ)/2)) =
      Real.exp (-p*h^2*(v : ℝ)/2)*Real.exp ((p*h)*x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [integral_const_mul]
  have hm := mgf_gaussianReal (μ:=0) (v:=v) (p:=gaussianReal 0 v)
    (X:=fun x : ℝ => x) (by simp) (p*h)
  rw [mgf] at hm
  rw [hm,← Real.exp_add]
  congr 1
  ring

theorem gaussianExponentialTilt_integral (h : ℝ) (v : ℝ≥0) :
    (∫ x, gaussianExponentialTilt h v x ∂gaussianReal 0 v)=1 := by
  simpa [gaussianExponentialTilt] using gaussianExponentialTilt_exponential_moment h 1 v

theorem gaussianExponentialTilt_integral_sq (h : ℝ) (v : ℝ≥0) :
    (∫ x, (gaussianExponentialTilt h v x)^2 ∂gaussianReal 0 v)=Real.exp (h^2*(v : ℝ)) := by
  have he (x : ℝ) : (gaussianExponentialTilt h v x)^2 =
      Real.exp (2*(h*x-h^2*(v : ℝ)/2)) := by
    rw [gaussianExponentialTilt, pow_two,← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  convert gaussianExponentialTilt_exponential_moment h 2 v using 1 <;> congr 1 <;> ring

end
end GinibrePoincare
