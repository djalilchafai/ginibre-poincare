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

 theorem correspondence_continuous_martingale_bounded_stopping_setIntegral
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M ℱ μ) (hcont : ∀ᵐ ω ∂μ, Continuous (fun t => M t ω))
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℝ≥0)))
    {T : ℝ≥0} (hτT : ∀ ω, τ ω ≤ T)
    {A : Set Ω} (hA : MeasurableSet[hτ.measurableSpace] A) :
    Integrable (fun ω => M (τ ω) ω) μ ∧
      (∫ ω in A, M (τ ω) ω ∂μ) = ∫ ω in A, M T ω ∂μ := by
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
  have hL1' : Tendsto (fun m => ∫⁻ ω, ‖f m ω - M (τ ω) ω‖ₑ ∂μ) atTop (𝓝 0) := by
    convert hL1 using 1
    funext m
    exact (eLpNorm_one_eq_lintegral_enorm ((hUI.memLp m).aestronglyMeasurable.sub hi.1)).symm
  have hint := tendsto_setIntegral_of_L1 (fun ω => M (τ ω) ω) hi.1
    (Eventually.of_forall (fun m => memLp_one_iff_integrable.mp (hUI.memLp m))) hL1' A
  have hle (m : ℕ) : (fun ω => (τ ω : WithTop ℝ≥0)) ≤ s m := by
    intro ω
    apply WithTop.coe_le_coe.mpr
    apply le_min _ (hτT ω)
    apply (le_div_iff₀ (by positivity : 0 < ((m+1 : ℕ) : ℝ≥0))).mpr
    simpa only [mul_comm] using (Nat.le_ceil (((m+1 : ℕ) : ℝ≥0)*τ ω))
  have heq (m : ℕ) : (∫ ω in A, f m ω ∂μ) = ∫ ω in A, M T ω ∂μ := by
    rw [setIntegral_congr_ae (hτ.measurableSpace_le A hA)
      ((he m).mono (fun _ h _ => h))]
    exact setIntegral_condExp (hs m).measurableSpace_le (hM.integrable T)
      (hτ.measurableSpace_mono (hs m) (hle m) A hA)
  refine ⟨hi, ?_⟩
  exact tendsto_nhds_unique hint (by simpa only [heq] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => ∫ ω in A, M T ω ∂μ)
      atTop (𝓝 (∫ ω in A, M T ω ∂μ))))

#print axioms correspondence_continuous_martingale_bounded_stopping_setIntegral
end
end GinibrePoincare
