module

public import GinibrePoincare.Analysis.GinibreStochasticProbabilityOperations

@[expose] public section

/-! Restricting genuine convergence in probability to any fixed event. -/
open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

theorem ginibre_tendstoInMeasure_indicator {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (E : Set Ω)
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ) (hf : TendstoInMeasure P f atTop g) :
    TendstoInMeasure P (fun n => E.indicator (f n)) atTop (E.indicator g) := by
  classical
  rw [tendstoInMeasure_iff_measureReal_norm] at hf ⊢
  intro ε hε
  apply squeeze_zero (fun n => measureReal_nonneg)
    (fun n => measureReal_mono (show
      {ω | ε ≤ ‖E.indicator (f n) ω-E.indicator g ω‖} ⊆ {ω | ε ≤ ‖f n ω-g ω‖} from by
        intro ω hω
        by_cases he : ω ∈ E
        · simpa only [Set.mem_setOf_eq, Set.indicator_of_mem he] using hω
        · simp only [Set.mem_setOf_eq, Set.indicator_of_notMem he, sub_self, norm_zero] at hω
          exact False.elim (not_le.mpr hε hω)))
    (hf ε hε)
end
end GinibrePoincare
