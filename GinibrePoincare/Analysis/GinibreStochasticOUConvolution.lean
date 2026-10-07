module

public import GinibrePoincare.Analysis.GinibreStochasticOURiemann
public import GinibrePoincare.Analysis.GinibreStochasticOUPath

@[expose] public section

/-! # The actual Brownian-driven OU path has the concrete transition law

The Gaussian law follows from finite Brownian increment sums, proved pathwise
convolution convergence, and bounded-characteristic dominated convergence.
-/
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

 theorem drivenOUPath_zero_weight_formula (rate : ℝ≥0) (t : ℝ) (N : ℝ → ℝ)
    (hzero : N 0 = 0) :
    drivenOUPath rate 0 (fun s => Real.sqrt (rate : ℝ) * N s) t =
      ginibreOUStochasticWeight rate t t * N t - ginibreOUStochasticWeight rate t 0 * N 0 -
        ∫ s in (0 : ℝ)..t, (rate : ℝ) * ginibreOUStochasticWeight rate t s * N s := by
  have hexp (s : ℝ) : Real.exp (-(rate : ℝ) * (t - s)) =
      Real.exp (-(rate : ℝ) * t) * Real.exp ((rate : ℝ) * s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hI : (∫ s in (0 : ℝ)..t, (rate : ℝ) * ginibreOUStochasticWeight rate t s * N s) =
      (Real.exp (-(rate : ℝ) * t) * (rate : ℝ)) *
        (∫ s in (0 : ℝ)..t, Real.exp ((rate : ℝ) * s) * (Real.sqrt (rate : ℝ) * N s)) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext s
    unfold ginibreOUStochasticWeight
    rw [hexp]
    ring
  rw [hI]
  simp only [drivenOUPath, drivenOUCorrection, smul_eq_mul, hzero,
    ginibreOUStochasticWeight, sub_self, mul_zero, Real.exp_zero, mul_one, sub_zero,
    zero_sub]
  ring

 theorem ginibreBrownianOURiemannSum_ae_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P)
    (rate t : ℝ≥0) :
    ∀ᵐ ω ∂P, Tendsto (fun n => ginibreBrownianOURiemannSum B rate t n ω) atTop
      (𝓝 (ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) 0 t ω)) := by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω hcont hzero
  let N : ℝ → ℝ := fun s => B s.toNNReal ω
  have hN : Continuous N := hcont.comp continuous_real_toNNReal
  have hN0 : N 0 = 0 := by simpa only [N, Real.toNNReal_zero] using hzero
  have hc : Continuous (fun s : ℝ => (rate : ℝ) * ginibreOUStochasticWeight rate t s) := by
    unfold ginibreOUStochasticWeight
    fun_prop
  have h := ginibreWeightedUniformIncrements_tendsto_integral
    (ginibreOUStochasticWeight rate t)
    (fun s => (rate : ℝ) * ginibreOUStochasticWeight rate t s)
    N (ginibreOUStochasticWeight_hasDerivAt rate t) hc hN t t.coe_nonneg
  simp only [smul_eq_mul] at h
  rw [← drivenOUPath_zero_weight_formula rate t N hN0] at h
  have hsum (n : ℕ) : ginibreBrownianOURiemannSum B rate t n ω =
      ∑ i ∈ Finset.range (n + 1), ginibreOUStochasticWeight rate t (ginibreUniformTime t n i) •
        (N (ginibreUniformTime t n (i + 1)) - N (ginibreUniformTime t n i)) := by
    unfold ginibreBrownianOURiemannSum
    simpa only [N, ginibreUniformBrownianTime, smul_eq_mul] using
      Fin.sum_univ_eq_sum_range (fun i => ginibreOUStochasticWeight rate t (ginibreUniformTime t n i) *
        (B (ginibreUniformBrownianTime t n (i + 1)) ω - B (ginibreUniformBrownianTime t n i) ω)) (n + 1)
  simp_rw [hsum, smul_eq_mul]
  exact h

 theorem ginibreBrownianOU_zero_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P)
    (rate t : ℝ≥0) :
    HasLaw (ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) 0 t)
      (ginibreOUTransition rate t 0) P := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hk : ginibreOUTransition rate t 0 = gaussianReal 0 (ginibreOUVariance rate t) := by
    change gaussianReal (ginibreOUDecay rate t * 0) (ginibreOUVariance rate t) = _
    rw [mul_zero]
  rw [hk]
  exact ginibreGaussian_hasLaw_of_ae_limit P
    (fun n => ginibreBrownianOURiemannSum B rate t n)
    (ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) 0 t)
    (fun _ => 0) (ginibreBrownianOURiemannVariance rate t) 0 (ginibreOUVariance rate t)
    (fun n => ginibreBrownianOURiemannSum_hasLaw B P hB.toIsPreBrownianReal rate t n)
    tendsto_const_nhds (ginibreBrownianOURiemannVariance_tendsto rate t)
    (ginibreBrownianOURiemannSum_ae_tendsto B P hB rate t)

/-- The actual continuous-noise driven solution has the exact OU kernel law
from every deterministic initial value. -/
theorem ginibreBrownianOU_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P)
    (rate t : ℝ≥0) (x : ℝ) :
    HasLaw (ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) x t)
      (ginibreOUTransition rate t x) P := by
  have h0 := ginibreBrownianOU_zero_hasLaw B P hB rate t
  have hk : ginibreOUTransition rate t 0 = gaussianReal 0 (ginibreOUVariance rate t) := by
    change gaussianReal (ginibreOUDecay rate t * 0) (ginibreOUVariance rate t) = _
    rw [mul_zero]
  rw [hk] at h0
  have h := gaussianReal_add_const h0 (ginibreOUDecay rate t * x)
  change HasLaw _ (gaussianReal (ginibreOUDecay rate t * x) (ginibreOUVariance rate t)) P
  simp only [zero_add] at h
  apply h.congr
  filter_upwards [] with ω
  simp only [ginibreBrownianOU, drivenOUPath, drivenOUCorrection, ginibreOUDecay, smul_eq_mul]
  ring

end
end GinibrePoincare
