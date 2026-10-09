module

public import GinibrePoincare.Analysis.BrownianIntegralGirsanovUniformIntegrability

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000

/-- True second-moment control plus actual convergence in probability preserves
normalization and gives L¹ convergence of nonnegative densities. -/
theorem nonnegativeDensities_limit_normalized_of_secondMoment_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (f n)) (hp : ∀ n ω, 0≤f n ω)
    (R : ℝ) (hR : 0≤R)
    (h2 : ∀ n, (∫⁻ ω, ENNReal.ofReal (f n ω)^2 ∂P) ≤ ENNReal.ofReal R)
    (h1 : ∀ n, (∫⁻ ω, ENNReal.ofReal (f n ω) ∂P)=1)
    (D : Ω → ℝ) (hlim : TendstoInMeasure P f atTop D) :
    Integrable D P ∧ (0≤ᵐ[P] D) ∧ (∫ ω, D ω ∂P)=1 ∧
      Tendsto (fun n => eLpNorm (f n-D) 1 P) atTop (𝓝 0) := by
  have hUI := nonnegativeDensities_uniformIntegrable_of_secondMoment_bound P f hm hp R hR h2
  have hDL := hUI.memLp_of_tendstoInMeasure hlim
  have hDi : Integrable D P := memLp_one_iff_integrable.mp hDL
  have hL := tendsto_Lp_finite_of_tendstoInMeasure (by norm_num : (1 : ℝ≥0∞)≤1)
    (by norm_num : (1 : ℝ≥0∞)≠∞) (fun n => (hm n).aestronglyMeasurable) hDL hUI.unifIntegrable hlim
  have hfn (n : ℕ) : Integrable (f n) P := memLp_one_iff_integrable.mp (hUI.memLp n)
  have hfi (n : ℕ) : (∫ ω, f n ω ∂P)=1 := by
    have hh := h1 n
    rw [← ofReal_integral_eq_lintegral_ofReal (hfn n) (Eventually.of_forall (hp n))] at hh
    have he := congrArg ENNReal.toReal hh
    simpa only [ENNReal.toReal_ofReal (integral_nonneg (hp n)), ENNReal.toReal_one] using he
  have hInt := tendsto_integral_of_L1' D (Eventually.of_forall hfn) hL
  have hDe : (∫ ω, D ω ∂P)=1 := by
    have hConst : Tendsto (fun n : ℕ => ∫ ω, f n ω ∂P) atTop (𝓝 1) := by
      simpa only [hfi] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
    exact tendsto_nhds_unique hInt hConst
  obtain ⟨s, hs, hsa⟩ := hlim.exists_seq_tendsto_ae
  have hDp : (0≤ᵐ[P] D) := by
    filter_upwards [hsa] with ω hω
    exact ge_of_tendsto hω (Eventually.of_forall (fun n => hp (s n) ω))
  exact ⟨hDi, hDp, hDe, hL⟩

end
end GinibrePoincare
