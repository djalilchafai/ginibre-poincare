module
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Centered real Gaussian laws are preserved by actual almost-everywhere
limits when their variances converge. The proof uses the bounded concrete
characteristic functions and dominated convergence. -/
theorem bakryBrownian_centered_gaussian_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (v : ℕ → ℝ≥0) (w : ℝ≥0) (hX : ∀ n, HasLaw (X n) (gaussianReal 0 (v n)) P)
    (hY : AEMeasurable Y P) (hLim : ∀ᵐ sample ∂P, Tendsto (fun n => X n sample) atTop (𝓝 (Y sample)))
    (hv : Tendsto v atTop (𝓝 w)) : HasLaw Y (gaussianReal 0 w) P := by
  refine ⟨hY,?_⟩
  apply Measure.ext_of_charFun
  funext t
  have hIntegral : Tendsto (fun n => ∫ sample, Complex.exp ((t*X n sample : ℝ)*Complex.I) ∂P)
      atTop (𝓝 (∫ sample, Complex.exp ((t*Y sample : ℝ)*Complex.I) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => 1)
    · intro n
      exact (Complex.continuous_exp.measurable.comp_aemeasurable
        ((Complex.measurable_ofReal.comp_aemeasurable ((hX n).aemeasurable.const_mul t)).mul_const Complex.I)).aestronglyMeasurable
    · exact integrable_const 1
    · intro n
      exact Eventually.of_forall (fun sample => by rw [Complex.norm_exp_ofReal_mul_I])
    · filter_upwards [hLim] with sample hs
      exact Complex.continuous_exp.continuousAt.tendsto.comp
        ((Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_const_nhds.mul hs)).mul_const Complex.I)
  have hCF (n : ℕ) : (∫ sample, Complex.exp ((t*X n sample : ℝ)*Complex.I) ∂P) =
      Complex.exp (-(v n : ℝ)*t^2/2 : ℂ) := by
    have hh := congrArg (fun μ : Measure ℝ => charFun μ t) (hX n).map_eq
    rw [charFun_apply_real, integral_map (hX n).aemeasurable (by fun_prop), charFun_gaussianReal] at hh
    simpa only [mul_zero, Complex.ofReal_zero, zero_mul, zero_sub, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_ofNat, Function.comp_def, neg_mul, neg_div] using hh
  have hExp : Tendsto (fun n => Complex.exp (-(v n : ℝ)*t^2/2 : ℂ)) atTop
      (𝓝 (Complex.exp (-(w : ℝ)*t^2/2 : ℂ))) := by
    apply Complex.continuous_exp.continuousAt.tendsto.comp
    exact (((Complex.continuous_ofReal.continuousAt.tendsto.comp
      (NNReal.continuous_coe.continuousAt.tendsto.comp hv)).neg.mul_const ((t : ℂ)^2)).div_const 2)
  have he := tendsto_nhds_unique (hIntegral.congr hCF) hExp
  rw [charFun_apply_real, integral_map hY (by fun_prop), charFun_gaussianReal]
  simpa only [mul_zero, Complex.ofReal_zero, zero_mul, zero_sub, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_ofNat, Function.comp_def, neg_mul, neg_div] using he

#print axioms bakryBrownian_centered_gaussian_limit
end
end GinibrePoincare
