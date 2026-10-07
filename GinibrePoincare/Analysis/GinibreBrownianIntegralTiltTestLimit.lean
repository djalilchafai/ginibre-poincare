module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralExponentialNatural
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal BoundedContinuousFunction
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- The subsequence criterion for actual convergence, without compactness assumptions. -/
theorem actualTendsto_of_subsequence_subsequence {E : Type*} [TopologicalSpace E]
    (f : ℕ → E) (x : E)
    (h : ∀ ns : ℕ → ℕ, StrictMono ns → ∃ ms : ℕ → ℕ, StrictMono ms ∧
      Tendsto (fun k => f (ns (ms k))) atTop (𝓝 x)) : Tendsto f atTop (𝓝 x) := by
  by_contra hn
  obtain ⟨s,hs,hfreq⟩ := not_tendsto_iff_exists_frequently_notMem.mp hn
  obtain ⟨ns,hns,hnot⟩ := extraction_of_frequently_atTop hfreq
  obtain ⟨ms,hms,hconv⟩ := h ns hns
  obtain ⟨k,hk⟩ := (hconv.eventually hs).exists
  exact hnot (ms k) hk

/-- L¹ density convergence controls actual integrals against arbitrary bounded
 measurable tests, even when the test changes with the approximation. -/
theorem actualDensity_bounded_test_error_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (D : ℕ → Ω → ℝ) (d : Ω → ℝ)
    (hDi : ∀ n, Integrable (D n) P) (hdi : Integrable d P)
    (hL : Tendsto (fun n => eLpNorm (D n-d) 1 P) atTop (𝓝 0))
    (b : ℕ → Ω → ℝ) (C : ℝ) (hC : 0≤C)
    (hb : ∀ n ω, ‖b n ω‖≤C) :
    Tendsto (fun n => ∫ ω, (D n ω-d ω)*b n ω ∂P) atTop (𝓝 0) := by
  have hnorm : Tendsto (fun n => ∫ ω, ‖D n ω-d ω‖ ∂P) atTop (𝓝 0) := by
    have ht := (ENNReal.continuousAt_toReal (by simp : (0:ℝ≥0∞)≠∞)).tendsto.comp hL
    have he (n : ℕ) : (∫ ω, ‖D n ω-d ω‖ ∂P) = (eLpNorm (D n-d) 1 P).toReal := by
      rw [eLpNorm_one_eq_lintegral_enorm ((hDi n).sub hdi).aestronglyMeasurable]
      simpa only [Pi.sub_apply] using integral_norm_eq_lintegral_enorm ((hDi n).sub hdi).aestronglyMeasurable
    simpa only [he,Function.comp_def,ENNReal.toReal_zero] using ht
  have hbound (n : ℕ) : ‖∫ ω, (D n ω-d ω)*b n ω ∂P‖ ≤ C*(∫ ω, ‖D n ω-d ω‖ ∂P) := by
    have hi := ((hDi n).sub hdi).norm.const_mul C
    have hh := norm_integral_le_of_norm_le (f := fun ω => (D n ω-d ω)*b n ω) hi (Eventually.of_forall (fun ω => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hb n ω) (norm_nonneg _)).trans_eq (mul_comm _ _)))
    simpa only [integral_const_mul,Pi.sub_apply] using hh
  apply squeeze_zero_norm (fun n => hbound n)
  simpa only [mul_zero] using hnorm.const_mul C

/-- An integrable density times bounded continuous tests respects actual
 convergence in probability, with no uniform-integrability certificate. -/
theorem actualDensity_continuous_test_tendsto {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsFiniteMeasure P] (d : Ω → ℝ) (hdi : Integrable d P)
    (X : ℕ → Ω → E) (x : Ω → E) (hX : ∀ n, AEMeasurable (X n) P)
    (hx : AEMeasurable x P) (hl : TendstoInMeasure P X atTop x) (b : E →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, d ω*b (X n ω) ∂P) atTop (𝓝 (∫ ω, d ω*b (x ω) ∂P)) := by
  apply actualTendsto_of_subsequence_subsequence
  intro ns hns
  obtain ⟨ms,hms,hae⟩ := (hl.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms,hms,?_⟩
  apply tendsto_integral_of_dominated_convergence (fun ω => ‖d ω‖*‖b‖)
  · intro n
    exact (hdi.aestronglyMeasurable.mul
      (b.continuous.measurable.comp_aemeasurable (hX _)).aestronglyMeasurable)
  · exact hdi.norm.mul_const _
  · intro n
    filter_upwards with ω
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (b.norm_coe_le_norm _) (norm_nonneg _)
  · filter_upwards [hae] with ω hω
    exact (b.continuous.tendsto _ |>.comp hω).const_mul _

end
end GinibrePoincare
