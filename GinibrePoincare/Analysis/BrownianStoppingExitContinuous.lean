module

public import GinibrePoincare.Analysis.BrownianStoppingExitApproximation
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

@[expose] public section

/-! Bounded optional sampling for continuous martingales in genuine continuous time. -/
open MeasureTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem continuous_martingale_bounded_stopping_integral
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M ℱ μ) (hcont : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    {T : ℝ≥0} (hτT : ∀ ω, τ ω ≤ T) :
    Integrable (fun ω => M (τ ω) ω) μ ∧
      (∫ ω, M (τ ω) ω ∂μ) = ∫ ω, M 0 ω ∂μ := by
  let q : ℕ → Ω → ℝ≥0 := fun m ω => min (stoppingUpperGrid m (τ ω)) T
  let s : ℕ → Ω → WithTop ℝ≥0 := fun m ω => (q m ω : WithTop ℝ≥0)
  have hs (m : ℕ) : IsStoppingTime ℱ (s m) := by
    simpa only [s, q, WithTop.coe_min] using (stoppingUpperGrid_isStoppingTime hτ m).min_const T
  have hb (m : ℕ) : ∀ ω, s m ω ≤ T := fun ω => by
    change ((min (stoppingUpperGrid m (τ ω)) T : ℝ≥0) : WithTop ℝ≥0) ≤ T
    exact_mod_cast (min_le_right (stoppingUpperGrid m (τ ω)) T)
  have hc (m : ℕ) : (Set.range (s m)).Countable := by
    have hr := (stoppingUpperGrid_countable_range m τ).image (fun t : WithTop ℝ≥0 => min t T)
    apply hr.mono
    rintro x ⟨ω, rfl⟩
    exact ⟨(stoppingUpperGrid m (τ ω) : WithTop ℝ≥0), ⟨ω, rfl⟩, by simp [s, q]⟩
  let f : ℕ → Ω → ℝ := fun m => stoppedValue M (s m)
  have he (m : ℕ) : f m =ᵐ[μ] μ[M T | (hs m).measurableSpace] :=
    hM.stoppedValue_ae_eq_condExp_of_le_const_of_countable_range (hs m) (hb m) (hc m)
  have hUI : UniformIntegrable f 1 μ := by
    exact (uniformIntegrable_congr_ae he).mpr
      ((hM.integrable T).uniformIntegrable_condExp (fun m => (hs m).measurableSpace_le_of_le (hb m)))
  have hlim : ∀ᵐ ω ∂μ, Tendsto (fun m => f m ω) atTop (𝓝 (M (τ ω) ω)) := by
    filter_upwards [hcont] with ω hω
    have ht := (stoppingUpperGrid_tendsto (τ ω)).min (tendsto_const_nhds (x := T))
    rw [min_eq_left (hτT ω)] at ht
    exact hω.continuousAt.tendsto.comp ht
  have hi := hUI.integrable_of_ae_tendsto hlim
  have hmeasure := tendstoInMeasure_of_tendsto_ae hUI.aestronglyMeasurable hlim
  have hL1 := tendsto_Lp_finite_of_tendstoInMeasure le_rfl ENNReal.one_ne_top
    hUI.aestronglyMeasurable (memLp_one_iff_integrable.mpr hi) hUI.unifIntegrable hmeasure
  have hint := tendsto_integral_of_L1' (fun ω => M (τ ω) ω)
    (Eventually.of_forall (fun m => memLp_one_iff_integrable.mp (hUI.memLp m))) hL1
  have heq (m : ℕ) : (∫ ω, f m ω ∂μ) = ∫ ω, M 0 ω ∂μ :=
    martingale_integral_stoppedValue_of_countable_range hM (hs m) (hb m) (hc m)
  refine ⟨hi, ?_⟩
  exact tendsto_nhds_unique hint (by simpa only [heq] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => ∫ ω, M 0 ω ∂μ) atTop (𝓝 (∫ ω, M 0 ω ∂μ))))

end
end GinibrePoincare
