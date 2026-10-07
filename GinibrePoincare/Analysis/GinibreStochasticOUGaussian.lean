module

public import GinibrePoincare.Analysis.GinibreStochasticOUInnovation
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

@[expose] public section

/-! # Gaussian finite-dimensional laws and covariance of the actual OU process -/
open MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem ginibreTimeChangedOU_zero_isGaussianProcess {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (rate : ℝ≥0) : IsGaussianProcess (ginibreTimeChangedOU B rate 0) P := by
  have h := (hB.isGaussianProcess.comp_right (ginibreOUBrownianClock rate)).smul
    (ginibreOUDecay rate)
  unfold ginibreTimeChangedOU
  simp only [zero_add]
  simpa only [smul_eq_mul, Function.comp_def] using h

 theorem ginibreTimeChangedOU_integral {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (rate t : ℝ≥0) (x : ℝ) :
    ∫ ω, ginibreTimeChangedOU B rate x t ω ∂P = ginibreOUDecay rate t * x := by
  rw [(ginibreTimeChangedOU_hasLaw B P hB rate x t).integral_eq]
  change (∫ y : ℝ, y ∂gaussianReal (ginibreOUDecay rate t * x)
    (ginibreOUVariance rate t)) = _
  exact integral_id_gaussianReal

 theorem ginibreTimeChangedOU_zero_covariance {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (rate s t : ℝ≥0) (hst : s ≤ t) :
    cov[ginibreTimeChangedOU B rate 0 s, ginibreTimeChangedOU B rate 0 t; P] =
      ginibreOUDecay rate (t - s) * (ginibreOUVariance rate s : ℝ) := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have he (v : ℝ≥0) : ginibreTimeChangedOU B rate 0 v =
      (fun ω => ginibreOUDecay rate v * B (ginibreOUBrownianClock rate v) ω) := by
    funext ω
    simp only [ginibreTimeChangedOU, zero_add]
  rw [he s, he t]
  change cov[(fun ω => ginibreOUDecay rate s * B (ginibreOUBrownianClock rate s) ω),
    (fun ω => ginibreOUDecay rate t * B (ginibreOUBrownianClock rate t) ω); P] = _
  rw [covariance_const_mul_left, covariance_const_mul_right, hB.covariance_eval,
    min_eq_left (ginibreOUBrownianClock_monotone rate hst)]
  have hd : ginibreOUDecay rate t =
      ginibreOUDecay rate (t - s) * ginibreOUDecay rate s := by
    rw [← ginibreOUDecay_add, add_tsub_cancel_of_le hst]
  have hv := congrArg (fun v : ℝ≥0 => (v : ℝ))
    (ginibreOUBrownianClock_variance rate s)
  simp only [NNReal.coe_mul, NNReal.coe_mk] at hv
  rw [hd]
  have hv2 := congrArg (fun z : ℝ => ginibreOUDecay rate (t - s) * z) hv
  nlinarith

/-- The actual two-time joint law, with a fresh independent Gaussian innovation.
This identifies the transition mechanism of the concrete Brownian process. -/
theorem ginibreTimeChangedOU_two_time_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (rate s t : ℝ≥0) (x : ℝ) :
    HasLaw (fun ω => (ginibreTimeChangedOU B rate x s ω,
      ginibreTimeChangedOU B rate x (s + t) ω))
      (((ginibreOUTransition rate s x).prod (gaussianReal 0 (ginibreOUVariance rate t))).map
        (fun p : ℝ × ℝ => (p.1, ginibreOUDecay rate t * p.1 + p.2))) P := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  let μ := (ginibreOUTransition rate s x).prod (gaussianReal 0 (ginibreOUVariance rate t))
  let F : ℝ × ℝ → ℝ × ℝ := fun p => (p.1, ginibreOUDecay rate t * p.1 + p.2)
  have hp := (ginibreOUInnovation_independent B P hB rate s t x).symm.hasLaw_prod
    (ginibreTimeChangedOU_hasLaw B P hB rate x s)
    (ginibreOUInnovation_hasLaw B P hB rate s t)
  have hF : HasLaw F (μ.map F) μ := ⟨by fun_prop, rfl⟩
  have h := hF.comp hp
  apply h.congr
  filter_upwards [] with ω
  change (ginibreTimeChangedOU B rate x s ω, ginibreTimeChangedOU B rate x (s + t) ω) =
    (ginibreTimeChangedOU B rate x s ω,
      ginibreOUDecay rate t * ginibreTimeChangedOU B rate x s ω + ginibreOUInnovation B rate s t ω)
  rw [ginibreTimeChangedOU_step]

end
end GinibrePoincare
