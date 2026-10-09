module
public import GinibrePoincare.Analysis.CorrespondenceDynamicsStoppingOptional
@[expose] public section
open Set MeasureTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
/-- Genuine continuous-time optional stopping preserves a continuous real
martingale. The proof tests every event in the original deterministic filtration. -/
theorem correspondenceOperator_continuous_stopped_martingale
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {M : ℝ≥0→Ω→ℝ}
    (hM : Martingale M F P) (hc : ∀ω, Continuous (fun t => M t ω))
    (τ : Ω→ℝ≥0) (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℝ≥0))) :
    Martingale (fun t ω => M (min (τ ω) t) ω) F P := by
  let N := fun t ω => M (min (τ ω) t) ω
  have had : StronglyAdapted F N := by
    have hh := hM.stronglyAdapted.stoppedProcess hc hτ
    have heq : stoppedProcess M (fun ω => (τ ω : WithTop ℝ≥0))=N := by
      funext t ω
      rw [stoppedProcess,← WithTop.coe_min]
      simp only [WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe, N, min_comm]
    rw [heq] at hh
    exact hh
  have hstop (t : ℝ≥0) : IsStoppingTime F (fun ω => (min (τ ω) t : WithTop ℝ≥0)) := by
    simpa only [WithTop.coe_min] using hτ.min_const t
  have hi (t : ℝ≥0) : Integrable (N t) P := by
    exact (correspondence_continuous_martingale_bounded_stopping_setIntegral hM
      (ae_of_all P hc) (hstop t) (fun ω => min_le_right (τ ω) t) MeasurableSet.univ).1
  refine ⟨had, fun s t hst => ?_⟩
  apply (ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (hi t)
    (fun _ _ _ => (hi s).integrableOn) ?_ (had s).aestronglyMeasurable).symm
  intro A hA _
  let E := {ω | τ ω≤s}
  have hE : MeasurableSet[F s] E := by
    simpa only [WithTop.coe_le_coe] using hτ s
  have hAm : MeasurableSet[F s] (A\E) := @MeasurableSet.diff Ω (F s) A E hA hE
  have hAtau : MeasurableSet[hτ.measurableSpace] (A\E) := by
    apply (hτ.measurableSet _).mpr
    refine ⟨le_iSup (fun t => (F t : MeasurableSpace Ω)) s _ hAm, fun u => ?_⟩
    by_cases hsu : s≤u
    · exact ((F.mono hsu) _ hAm).inter (hτ u)
    · have he : (A\E)∩{ω | (τ ω : WithTop ℝ≥0)≤u}=∅ := by
        ext ω
        simp only [mem_inter_iff, Set.mem_sdiff, Set.mem_ofPred_eq, WithTop.coe_le_coe, mem_empty_iff_false]
        constructor
        · rintro ⟨⟨_, hnot⟩, hle⟩
          exact hnot (hle.trans (le_of_lt (lt_of_not_ge hsu)))
        · exact False.elim
      rw [he]
      exact @MeasurableSet.empty Ω (F u)
  have hArho : MeasurableSet[(hstop s).measurableSpace] (A\E) := by
    apply (hτ.measurableSet_min_const_iff _).mpr
    exact ⟨hAtau, hAm⟩
  have hAsigma : MeasurableSet[(hstop t).measurableSpace] (A\E) := by
    apply (hτ.measurableSet_min_const_iff _).mpr
    exact ⟨hAtau, (F.mono hst) _ hAm⟩
  have heqplus : (∫ ω in A\E, N s ω ∂P) = ∫ ω in A\E, N t ω ∂P := by
    rw [(correspondence_continuous_martingale_bounded_stopping_setIntegral hM
      (ae_of_all P hc) (hstop s) (fun ω => min_le_right (τ ω) s) hArho).2,
      (correspondence_continuous_martingale_bounded_stopping_setIntegral hM
      (ae_of_all P hc) (hstop t) (fun ω => min_le_right (τ ω) t) hAsigma).2]
    exact hM.setIntegral_eq hst hAm
  have heqminus : (∫ ω in A∩E, N s ω ∂P)=∫ ω in A∩E, N t ω ∂P := by
    apply setIntegral_congr_fun ((F.le s) _ (@MeasurableSet.inter Ω (F s) A E hA hE))
    intro ω hω
    have hle : τ ω≤s := hω.2
    simp only [N, min_eq_left hle, min_eq_left (hle.trans hst)]
  rw [← integral_inter_add_sdiff ((F.le s) _ hE) (hi s).integrableOn,
    ← integral_inter_add_sdiff ((F.le s) _ hE) (hi t).integrableOn, heqplus, heqminus]
#print axioms correspondenceOperator_continuous_stopped_martingale
end
end GinibrePoincare
