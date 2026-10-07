module

public import GinibrePoincare.Analysis.GinibreStochasticCIRMoments

@[expose] public section

/-! # Genuine Gaussian fourth moments for Brownian quadratic-increment estimates -/
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

 theorem ginibreGaussian_centered_fourthMoment (v : ℝ≥0) :
    (∫ x : ℝ, x^4 ∂gaussianReal 0 v) = 3*(v : ℝ)^2 := by
  have hMom := iteratedDeriv_mgf_zero (X := id) (μ := gaussianReal 0 v) (by simp) 4
  change iteratedDeriv 4 (mgf (fun x : ℝ => x) (gaussianReal 0 v)) 0 = (∫ x : ℝ, x^4 ∂gaussianReal 0 v) at hMom
  rw [mgf_fun_id_gaussianReal] at hMom
  simp only [zero_mul, zero_add, id_eq, Pi.pow_apply] at hMom
  rw [← hMom]
  let g := fun t : ℝ => Real.exp ((v : ℝ)*t^2/2)
  have hExp (t : ℝ) : HasDerivAt g ((v : ℝ)*t*g t) t := by
    convert! ((((hasDerivAt_id t).pow 2).const_mul (v : ℝ)).div_const 2).exp using 1 <;> dsimp [g] <;> ring
  have h1 : deriv g = fun t => (v : ℝ)*t*g t := funext (fun t => (hExp t).deriv)
  have h2 : deriv (fun t => (v : ℝ)*t*g t) = fun t => ((v : ℝ)+(v : ℝ)^2*t^2)*g t := by
    funext t
    have h := (((hasDerivAt_id t).const_mul (v : ℝ)).mul (hExp t)).deriv
    convert! h using 1 <;> dsimp only [id_eq, Pi.pow_apply] <;> ring
  have h3 : deriv (fun t => ((v : ℝ)+(v : ℝ)^2*t^2)*g t) =
      fun t => (3*(v : ℝ)^2*t+(v : ℝ)^3*t^3)*g t := by
    funext t
    have h := (((((hasDerivAt_id t).pow 2).const_mul ((v : ℝ)^2)).const_add (v : ℝ)).mul (hExp t)).deriv
    convert! h using 1 <;> dsimp only [id_eq, Pi.pow_apply] <;> ring
  have h4 : deriv (fun t => (3*(v : ℝ)^2*t+(v : ℝ)^3*t^3)*g t) 0 = 3*(v : ℝ)^2 := by
    have h := ((((hasDerivAt_id (0 : ℝ)).const_mul (3*(v : ℝ)^2)).add
      (((hasDerivAt_id (0 : ℝ)).pow 3).const_mul ((v : ℝ)^3))).mul (hExp 0)).deriv
    convert! h using 1 <;> simp [g]
  change iteratedDeriv 4 g 0 = _
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [h1, h2, h3, h4]

end
end GinibrePoincare
