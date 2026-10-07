module

public import GinibrePoincare.Analysis.BrownianStoppingExitApproximation
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

@[expose] public section

/-! Evaluating an adapted process at a bounded countable-range random time. -/
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

 theorem adapted_countable_time_evaluation_measurable {Ω E : Type*}
    [mAmbient : MeasurableSpace Ω] [MeasurableSpace E]
    (F : Filtration ℝ≥0 mAmbient) (u : ℝ≥0 → Ω → E)
    (hu : Adapted F u) (s : ℝ≥0) (q : Ω → ℝ≥0)
    (hq : @Measurable Ω ℝ≥0 (F s) _ q) (hcount : (Set.range q).Countable)
    (hbound : ∀ ω, q ω ≤ s) : @Measurable Ω E (F s) _ (fun ω => u (q ω) ω) := by
  haveI : Countable (Set.range q) := hcount.to_subtype
  have hEval : @Measurable (Ω × Set.range q) E
      (@Prod.instMeasurableSpace Ω (Set.range q) (F s) _) _
      (fun p => u p.2 p.1) := by
    apply measurable_from_prod_countable_left
    intro t
    obtain ⟨ω, hω⟩ := t.property
    have ht : t.val ≤ s := by rw [← hω]; exact hbound ω
    exact (hu t).mono (F.mono ht) le_rfl
  exact hEval.comp (measurable_id.prodMk (hq.subtype_mk (h := fun ω => Set.mem_range_self ω)))

 theorem adapted_capped_upper_grid_evaluation_measurable {Ω E : Type*}
    [mAmbient : MeasurableSpace Ω] [MeasurableSpace E]
    (F : Filtration ℝ≥0 mAmbient) (u : ℝ≥0 → Ω → E)
    (hu : Adapted F u) (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime F (fun ω => (σ ω : WithTop ℝ≥0))) (m : ℕ) (s : ℝ≥0) :
    @Measurable Ω E (F s) _ (fun ω => u (min s (stoppingUpperGrid m (σ ω))) ω) := by
  let q := fun ω => min s (stoppingUpperGrid m (σ ω))
  have hStop := (stoppingUpperGrid_isStoppingTime hσ m).min_const s
  have hm := hStop.measurable_of_le (fun ω => min_le_right _ _)
  have hq : @Measurable Ω ℝ≥0 (F s) _ q := by
    have h := ENNReal.measurable_toNNReal.comp hm
    convert h using 1
    funext ω
    change min s (stoppingUpperGrid m (σ ω)) =
      (min (stoppingUpperGrid m (σ ω) : ℝ≥0∞) (s : ℝ≥0∞)).toNNReal
    rw [← ENNReal.coe_min, ENNReal.toNNReal_coe, min_comm]
  have hcount : (Set.range q).Countable := by
    apply (Set.countable_range (fun k : ℕ => min s
      ((k : ℝ≥0)/((m+1 : ℕ) : ℝ≥0)))).mono
    rintro x ⟨ω, rfl⟩
    exact ⟨Nat.ceil (((m+1 : ℕ) : ℝ≥0)*σ ω), rfl⟩
  exact adapted_countable_time_evaluation_measurable F u hu s q hq hcount
    (fun ω => min_le_left _ _)

end
end GinibrePoincare
