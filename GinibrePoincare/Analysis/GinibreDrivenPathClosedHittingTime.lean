module

public import GinibrePoincare.Analysis.GinibreStochasticCausalFlowAdaptation
public import Mathlib.Probability.Process.HittingTime

@[expose] public section

/-! Actual first hitting times of closed sets along continuous paths attain their boundary. -/
open Set MeasureTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000

theorem drivenContinuous_closed_hitting_mem {Ω E : Type*} [TopologicalSpace E]
    (u : ℝ≥0 → Ω → E) (S : Set E) (hS : IsClosed S) (T : ℝ≥0) (ω : Ω)
    (hu : Continuous (fun t => u t ω)) (hHit : ∃ j ∈ Icc 0 T, u j ω ∈ S) :
    u (hittingBtwn u S 0 T ω) ω ∈ S := by
  classical
  have hne : (Icc 0 T ∩ {j | u j ω ∈ S}).Nonempty := by
    obtain ⟨j, hj, hSj⟩ := hHit
    exact ⟨j, hj, hSj⟩
  have hb : BddBelow (Icc 0 T ∩ {j | u j ω ∈ S}) := ⟨0, fun j hj => hj.1.1⟩
  have hm := (isClosed_Icc.inter (hS.preimage hu)).csInf_mem hne hb
  change u (if ∃ j ∈ Icc 0 T, u j ω ∈ S then sInf (Icc 0 T ∩ {j | u j ω ∈ S}) else T) ω ∈ S
  rw [if_pos hHit]
  exact hm.2

theorem drivenContinuous_closed_hitting_le_iff {Ω E : Type*} [TopologicalSpace E]
    (u : ℝ≥0 → Ω → E) (S : Set E) (hS : IsClosed S) (T t : ℝ≥0) (ω : Ω)
    (hu : Continuous (fun t => u t ω)) :
    hittingBtwn u S 0 T ω ≤ t ↔ T ≤ t ∨ ∃ j ∈ Icc 0 t, u j ω ∈ S := by
  classical
  constructor
  · intro hτ
    by_cases hT : T ≤ t
    · exact Or.inl hT
    · right
      have hHit : ∃ j ∈ Icc 0 T, u j ω ∈ S := by
        by_contra hn
        change (if ∃ j ∈ Icc 0 T, u j ω ∈ S then sInf (Icc 0 T ∩ {j | u j ω ∈ S}) else T) ≤ t at hτ
        rw [if_neg hn] at hτ
        exact hT hτ
      exact ⟨hittingBtwn u S 0 T ω, ⟨bot_le, hτ⟩,
        drivenContinuous_closed_hitting_mem u S hS T ω hu hHit⟩
  · rintro (hT | ⟨j, hj, hSj⟩)
    · exact (hittingBtwn_le (u := u) (s := S) (n := 0) (m := T) ω).trans hT
    · by_cases hT : T ≤ t
      · exact (hittingBtwn_le (u := u) (s := S) (n := 0) (m := T) ω).trans hT
      · exact (hittingBtwn_le_of_mem (u := u) (s := S) hj.1
          (hj.2.trans (le_of_not_ge hT)) hSj).trans hj.2

theorem drivenContinuous_closed_hitting_pos {Ω E : Type*} [TopologicalSpace E]
    (u : ℝ≥0 → Ω → E) (S : Set E) (hS : IsClosed S) (T : ℝ≥0) (hT : 0 < T)
    (ω : Ω) (hu : Continuous (fun t => u t ω)) (h0 : u 0 ω ∉ S) :
    0 < hittingBtwn u S 0 T ω := by
  classical
  by_contra hn
  have hz : hittingBtwn u S 0 T ω = 0 := le_antisymm (le_of_not_gt hn) (bot_le)
  have h := (drivenContinuous_closed_hitting_le_iff u S hS T 0 ω hu).mp hz.le
  rcases h with h | ⟨j, hj, hSj⟩
  · exact (not_le_of_gt hT) h
  · have hj0 : j = 0 := le_antisymm hj.2 (bot_le)
    exact h0 (hj0 ▸ hSj)


theorem drivenContinuous_norm_le_until_hitting {Ω E : Type*} [NormedAddCommGroup E]
    (u : ℝ≥0 → Ω → E) (r : ℝ) (T : ℝ≥0) (ω : Ω)
    (hu : Continuous (fun t => u t ω)) (h0 : ‖u 0 ω‖ ≤ r)
    (t : ℝ≥0) (ht : t ≤ hittingBtwn u {x | r ≤ ‖x‖} 0 T ω) : ‖u t ω‖ ≤ r := by
  by_contra hn
  have hrt : r < ‖u t ω‖ := lt_of_not_ge hn
  obtain ⟨j, hj, hjr⟩ := intermediate_value_Icc (bot_le : (0 : ℝ≥0) ≤ t)
    hu.norm.continuousOn ⟨h0, hrt.le⟩
  have hjt : j < t := lt_of_le_of_ne hj.2 (by intro he; rw [he] at hjr; linarith)
  have hjT : j ≤ T := hj.2.trans (ht.trans (hittingBtwn_le (u := u) (s := {x | r ≤ ‖x‖}) (n := 0) (m := T) ω))
  have hτj := hittingBtwn_le_of_mem (u := u) (s := {x | r ≤ ‖x‖}) (n := 0) (m := T)
    (i := j) (ω := ω) hj.1 hjT (show u j ω ∈ {x | r ≤ ‖x‖} from hjr.ge)
  exact (not_lt_of_ge (ht.trans hτj)) hjt

end
end GinibrePoincare
