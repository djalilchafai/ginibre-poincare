module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsReversalVolterra
@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
local instance bakryGibbsSurvival_pathMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
local instance bakryGibbsSurvival_pathBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩

def bakryEmeryGibbsCompactSurvival (n : ℕ) (T : ℝ≥0) (R : ℝ) :
    Set C(Icc (0 : ℝ) (T : ℝ), Configuration n) := {x | ‖x‖ < R}

theorem bakryEmeryGibbsCompactSurvival_mem (n : ℕ) (T : ℝ≥0) (R : ℝ)
    (x : C(Icc (0 : ℝ) (T : ℝ), Configuration n)) :
    x ∈ bakryEmeryGibbsCompactSurvival n T R ↔ ∀ t, ‖x t‖ < R := by
  letI : Nonempty (Icc (0 : ℝ) (T : ℝ)) := ⟨⟨0,⟨le_rfl,T.property⟩⟩⟩
  exact x.norm_lt_iff_of_nonempty

theorem bakryEmeryGibbsCompactSurvival_measurableSet (n : ℕ) (T : ℝ≥0) (R : ℝ) :
    MeasurableSet (bakryEmeryGibbsCompactSurvival n T R) :=
  (isOpen_lt continuous_norm continuous_const).measurableSet

theorem bakryEmeryGibbsCompactSurvival_exhaustion (n : ℕ) (T : ℝ≥0) :
    (⋃ k : ℕ, bakryEmeryGibbsCompactSurvival n T (k : ℝ)) = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨k,hk⟩ := exists_nat_gt ‖x‖
  exact mem_iUnion.mpr ⟨k,hk⟩


theorem bakryEmeryGibbsCompactSurvival_reverse (n : ℕ) (T : ℝ≥0) (R : ℝ)
    (x : C(Icc (0 : ℝ) (T : ℝ), Configuration n)) :
    x.comp (ginibreHamiltonianCompactReverseTime T T.property) ∈ bakryEmeryGibbsCompactSurvival n T R ↔
      x ∈ bakryEmeryGibbsCompactSurvival n T R := by
  rw [bakryEmeryGibbsCompactSurvival_mem, bakryEmeryGibbsCompactSurvival_mem]
  constructor
  · intro h t
    let s := ginibreHamiltonianCompactReverseTime T T.property t
    have he : ginibreHamiltonianCompactReverseTime T T.property s = t := by
      apply Subtype.ext
      change (T : ℝ)-((T : ℝ)-t.val) = t.val
      ring
    simpa only [ContinuousMap.comp_apply, he] using h s
  · intro h t
    exact h _

def bakryEmeryGibbsKilledOUAction {n : ℕ} (W : Configuration n → ℝ)
    (T : ℝ≥0) (R : ℝ) : C(Icc (0 : ℝ) (T : ℝ), Configuration n) → ℝ≥0∞ :=
  (bakryEmeryGibbsCompactSurvival n T R).indicator (bakryEmeryGibbsOUAction W T T.property)

theorem bakryEmeryGibbsKilledOUAction_measurable {n : ℕ} (W : Configuration n → ℝ)
    (hW : ContDiff ℝ 2 W) (T : ℝ≥0) (R : ℝ) :
    Measurable (bakryEmeryGibbsKilledOUAction W T R) :=
  (bakryEmeryGibbsOUAction_measurable hW T T.property).indicator
    (bakryEmeryGibbsCompactSurvival_measurableSet n T R)

theorem bakryEmeryGibbsKilledOUAction_reverse {n : ℕ} (W : Configuration n → ℝ)
    (T : ℝ≥0) (R : ℝ) (x : C(Icc (0 : ℝ) (T : ℝ), Configuration n)) :
    bakryEmeryGibbsKilledOUAction W T R (x.comp (ginibreHamiltonianCompactReverseTime T T.property)) =
      bakryEmeryGibbsKilledOUAction W T R x := by
  unfold bakryEmeryGibbsKilledOUAction
  by_cases h : x ∈ bakryEmeryGibbsCompactSurvival n T R
  · rw [indicator_of_mem h, indicator_of_mem ((bakryEmeryGibbsCompactSurvival_reverse n T R x).mpr h)]
    exact bakryEmeryGibbsOUAction_reverse W T T.property x
  · rw [indicator_of_notMem h, indicator_of_notMem (by
      intro hh; exact h ((bakryEmeryGibbsCompactSurvival_reverse n T R x).mp hh))]

/-- Actual closed-ball exits couple literal compact survival, including a
hit at the terminal time. -/
theorem bakryEmeryGibbs_closed_exit_survival {E : Type*} [NormedAddCommGroup E]
    (U X : ℝ≥0 → E) (hU : Continuous U) (z : E) (r : ℝ) (T : ℝ≥0)
    (hEq : ∀ t ≤ hittingBtwn (fun s (_ : Unit) => U s-z) {v | r ≤ ‖v‖} 0 T (), X t = U t) :
    (∀ t ≤ T, ‖X t-z‖ < r) ↔ (∀ t ≤ T, ‖U t-z‖ < r) := by
  let V : ℝ≥0 → Unit → E := fun t _ => U t-z
  let θ := hittingBtwn V {v | r ≤ ‖v‖} 0 T ()
  have hθ : θ ≤ T := hittingBtwn_le ()
  have hNoHit (h : ∀ t ≤ T, ‖U t-z‖ < r) :
      ¬ ∃ t ∈ Icc 0 T, V t () ∈ {v | r ≤ ‖v‖} := by
    rintro ⟨t,ht,hmem⟩
    exact (not_le_of_gt (h t ht.2)) hmem
  have hEnd (h : ∀ t ≤ T, ‖U t-z‖ < r) : θ = T := by
    unfold θ hittingBtwn
    rw [if_neg (hNoHit h)]
  constructor
  · intro hX
    by_contra h
    push_neg at h
    obtain ⟨t,ht,hh⟩ := h
    have hHit : ∃ t ∈ Icc 0 T, V t () ∈ {v | r ≤ ‖v‖} := ⟨t,⟨bot_le,ht⟩,hh⟩
    have hm := drivenContinuous_closed_hitting_mem V {v | r ≤ ‖v‖}
      (isClosed_le continuous_const continuous_norm) T () (hU.sub continuous_const) hHit
    have he := hEq θ le_rfl
    exact (not_le_of_gt (hX θ hθ)) (by change r ≤ ‖U θ-z‖ at hm; simpa only [he] using hm)
  · intro h t ht
    rw [hEq t (by change t ≤ θ; rw [hEnd h]; exact ht)]
    exact h t ht

/-- Any literal domain inside the stopping ball has identical survival for
paths coupled up to the actual exit. In particular the domain may be a fixed
ball centered at zero, independent of the sampled initial state. -/
theorem bakryEmeryGibbs_closed_exit_domain_survival {E : Type*} [NormedAddCommGroup E]
    (U X : ℝ≥0 → E) (hU : Continuous U) (z : E) (r : ℝ) (T : ℝ≥0)
    (G : Set E) (hG : ∀ v ∈ G, ‖v-z‖ < r)
    (hEq : ∀ t ≤ hittingBtwn (fun s (_ : Unit) => U s-z) {v | r ≤ ‖v‖} 0 T (), X t = U t) :
    (∀ t ≤ T, X t ∈ G) ↔ (∀ t ≤ T, U t ∈ G) := by
  have hiff := bakryEmeryGibbs_closed_exit_survival U X hU z r T hEq
  have hEnd (h : ∀ t ≤ T, ‖U t-z‖ < r) :
      hittingBtwn (fun s (_ : Unit) => U s-z) {v | r ≤ ‖v‖} 0 T () = T := by
    unfold hittingBtwn
    rw [if_neg]
    rintro ⟨t,ht,hh⟩
    exact (not_le_of_gt (h t ht.2)) hh
  constructor
  · intro hX
    have he := hEnd (hiff.mp (fun t ht => hG _ (hX t ht)))
    intro t ht
    rw [← hEq t (by rw [he]; exact ht)]
    exact hX t ht
  · intro hUmem
    have he := hEnd (fun t ht => hG _ (hUmem t ht))
    intro t ht
    rw [hEq t (by rw [he]; exact ht)]
    exact hUmem t ht

#print axioms bakryEmeryGibbsKilledOUAction_measurable
#print axioms bakryEmeryGibbsKilledOUAction_reverse
#print axioms bakryEmeryGibbsCompactSurvival_reverse
#print axioms bakryEmeryGibbsCompactSurvival_mem
#print axioms bakryEmeryGibbsCompactSurvival_measurableSet
#print axioms bakryEmeryGibbsCompactSurvival_exhaustion
#print axioms bakryEmeryGibbs_closed_exit_domain_survival
#print axioms bakryEmeryGibbs_closed_exit_survival
end
end GinibrePoincare
