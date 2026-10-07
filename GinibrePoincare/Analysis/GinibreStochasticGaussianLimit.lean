module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! # Gaussian laws of almost-sure limits

Bounded characteristic functions identify the limiting law without imposing
an unproved integrable bound on the sample-path supremum.
-/
open MeasureTheory ProbabilityTheory Filter BoundedContinuousFunction
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem ginibreGaussian_hasLaw_of_ae_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (m : ℕ → ℝ) (v : ℕ → ℝ≥0) (m₀ : ℝ) (v₀ : ℝ≥0)
    (hLaw : ∀ n, HasLaw (X n) (gaussianReal (m n) (v n)) P)
    (hm : Tendsto m atTop (𝓝 m₀)) (hv : Tendsto v atTop (𝓝 v₀))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    HasLaw Y (gaussianReal m₀ v₀) P := by
  have hY : AEMeasurable Y P := aemeasurable_of_tendsto_metrizable_ae
    atTop (fun n => (hLaw n).aemeasurable) hlim
  refine ⟨hY, Measure.ext_of_charFun ?_⟩
  funext t
  let φ := innerProbChar t
  have hbound : ∀ y : ℝ, ‖φ y‖ ≤ 1 := by
    intro y
    simpa [φ, innerProbChar_apply, Complex.ofReal_mul] using
      le_of_eq (Complex.norm_exp_ofReal_mul_I (t * y))
  have hI := tendsto_integral_of_dominated_convergence (fun _ : Ω => (1 : ℝ))
    (fun n => φ.continuous.comp_aestronglyMeasurable (hLaw n).aemeasurable.aestronglyMeasurable)
    (integrable_const 1) (fun n => Filter.Eventually.of_forall fun ω => hbound (X n ω))
    (hlim.mono fun ω hω => φ.continuous.continuousAt.tendsto.comp hω)
  have hc : Continuous (fun p : ℝ × ℝ≥0 =>
      Complex.exp ((t : ℂ) * (p.1 : ℂ) * Complex.I - (p.2 : ℂ) * (t : ℂ) ^ 2 / 2)) := by
    fun_prop
  have hG := (hc.tendsto (m₀, v₀)).comp (hm.prodMk_nhds hv)
  have he (n : ℕ) : (∫ ω, φ (X n ω) ∂P) = charFun (gaussianReal (m n) (v n)) t := by
    rw [charFun_eq_integral_innerProbChar, ← (hLaw n).map_eq,
      integral_map (hLaw n).aemeasurable (φ.continuous.aestronglyMeasurable)]
  simp_rw [he, charFun_gaussianReal] at hI
  have hi := tendsto_nhds_unique hI hG
  rw [charFun_eq_integral_innerProbChar, integral_map hY (φ.continuous.aestronglyMeasurable),
    charFun_gaussianReal]
  exact hi

end
end GinibrePoincare
