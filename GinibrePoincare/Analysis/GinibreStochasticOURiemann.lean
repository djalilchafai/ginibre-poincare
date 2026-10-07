module

public import GinibrePoincare.Analysis.GinibreStochasticBrownianSums
public import GinibrePoincare.Analysis.GinibreStochasticOUWeight
public import GinibrePoincare.Analysis.GinibreDrivenPathUniformPartition

@[expose] public section

/-! # Concrete weighted Brownian sums approaching the OU convolution -/
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 def ginibreUniformBrownianTime (t : ℝ≥0) (n i : ℕ) : ℝ≥0 :=
  (ginibreUniformTime t n i).toNNReal

 theorem ginibreUniformBrownianTime_coe (t : ℝ≥0) (n i : ℕ) :
    (ginibreUniformBrownianTime t n i : ℝ) = ginibreUniformTime t n i := by
  apply Real.coe_toNNReal
  unfold ginibreUniformTime
  positivity

 theorem ginibreUniformBrownianTime_mono (t : ℝ≥0) (n : ℕ) :
    Monotone (ginibreUniformBrownianTime t n) := by
  intro i j hij
  exact Real.toNNReal_mono (ginibreUniformTime_mono t t.coe_nonneg n hij)

 def ginibreBrownianOURiemannSum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (rate t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i : Fin (n + 1), ginibreOUStochasticWeight rate t (ginibreUniformTime t n i) *
    (B (ginibreUniformBrownianTime t n (i.val + 1)) ω -
      B (ginibreUniformBrownianTime t n i) ω)

 def ginibreBrownianOURiemannVariance (rate t : ℝ≥0) (n : ℕ) : ℝ≥0 :=
  ∑ i : Fin (n + 1),
    NNReal.mk (ginibreOUStochasticWeight rate t (ginibreUniformTime t n i) ^ 2) (sq_nonneg _) *
      (ginibreUniformBrownianTime t n (i.val + 1) - ginibreUniformBrownianTime t n i)

 theorem ginibreBrownianOURiemannSum_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (rate t : ℝ≥0) (n : ℕ) :
    HasLaw (ginibreBrownianOURiemannSum B rate t n)
      (gaussianReal 0 (ginibreBrownianOURiemannVariance rate t n)) P := by
  exact ginibreBrownian_weighted_increments_hasLaw B P hB (n + 1)
    (fun i => ginibreUniformBrownianTime t n i)
    ((ginibreUniformBrownianTime_mono t n).comp Fin.val_strictMono.monotone)
    (fun i => ginibreOUStochasticWeight rate t (ginibreUniformTime t n i))

 theorem ginibreBrownianOURiemannVariance_coe (rate t : ℝ≥0) (n : ℕ) :
    (ginibreBrownianOURiemannVariance rate t n : ℝ) =
      ∑ i ∈ Finset.range (n + 1),
        ginibreOUStochasticWeight rate t (ginibreUniformTime t n i) ^ 2 *
          (ginibreUniformTime t n (i + 1) - ginibreUniformTime t n i) := by
  unfold ginibreBrownianOURiemannVariance
  simp only [NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_mk]
  simp_rw [NNReal.coe_sub (ginibreUniformBrownianTime_mono t n (Nat.le_succ _)),
    ginibreUniformBrownianTime_coe]
  exact Fin.sum_univ_eq_sum_range (fun i =>
    ginibreOUStochasticWeight rate t (ginibreUniformTime t n i) ^ 2 *
      (ginibreUniformTime t n (i + 1) - ginibreUniformTime t n i)) (n + 1)

 theorem ginibreBrownianOURiemannVariance_tendsto (rate t : ℝ≥0) :
    Tendsto (ginibreBrownianOURiemannVariance rate t) atTop (𝓝 (ginibreOUVariance rate t)) := by
  have hc : Continuous (fun s : ℝ =>
      2 * (rate : ℝ) * ginibreOUStochasticWeight rate t s ^ 2) := by
    unfold ginibreOUStochasticWeight
    fun_prop
  have h := ginibreUniformScalarRiemann_tendsto
    (fun s => ginibreOUStochasticWeight rate t s ^ 2)
    (fun s => 2 * (rate : ℝ) * ginibreOUStochasticWeight rate t s ^ 2)
    (ginibreOUStochasticWeight_sq_hasDerivAt rate t) hc t t.coe_nonneg
  rw [ginibreOUStochasticWeight_variance_integral] at h
  have he := (continuous_real_toNNReal.tendsto (ginibreOUVariance rate t : ℝ)).comp h
  simpa only [Function.comp_def, ← ginibreBrownianOURiemannVariance_coe, Real.toNNReal_coe] using he

end
end GinibrePoincare
