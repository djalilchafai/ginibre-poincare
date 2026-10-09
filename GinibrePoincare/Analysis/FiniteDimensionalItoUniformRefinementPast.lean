module

public import GinibrePoincare.Analysis.FiniteDimensionalItoUniformRefinement
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

@[expose] public section

open MeasureTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- Actual restriction of a fine past history to an earlier past. -/
def itoPastRestriction {X : Type*} (s t : ℝ≥0) (hst : s ≤ t)
    (p : Set.Iic t → X) : Set.Iic s → X := fun u => p ⟨u.val, u.property.trans hst⟩

theorem itoPastRestriction_measurable {X : Type*} [MeasurableSpace X]
    (s t : ℝ≥0) (hst : s ≤ t) : Measurable (itoPastRestriction (X := X) s t hst) := by
  apply measurable_pi_lambda
  intro u
  exact measurable_pi_apply _

/-- The true coarse block index of a fine interval. -/
def itoUniformCoarseIndex (N M : ℕ) (hM : 0 < M) (k : Fin (N*M)) : Fin N :=
  ⟨k.val/M, (Nat.div_lt_iff_lt_mul hM).mpr k.is_lt⟩

/-- Genuine common-refinement predictable coefficient, using actual past restriction. -/
def itoUniformRefinedCoefficient {X : Type*} (T : ℝ≥0) (N M : ℕ) (hM : 0 < M)
    (F : (i : Fin N) → (Set.Iic (itoUniformNNTime T N i) → X) → ℝ)
    (k : Fin (N*M)) : (Set.Iic (itoUniformNNTime T (N*M) k) → X) → ℝ :=
  fun p => F (itoUniformCoarseIndex N M hM k)
    (itoPastRestriction (itoUniformNNTime T N (k.val/M)) (itoUniformNNTime T (N*M) k)
      (itoUniformNNTime_coarse_le_fine T N M k hM) p)

/-- Coarse measurable predictable weights remain genuinely measurable on the fine past. -/
theorem itoUniformRefinedCoefficient_measurable {X : Type*} [MeasurableSpace X]
    (T : ℝ≥0) (N M : ℕ) (hM : 0 < M)
    (F : (i : Fin N) → (Set.Iic (itoUniformNNTime T N i) → X) → ℝ)
    (hF : ∀ i, Measurable (F i)) (k : Fin (N*M)) :
    Measurable (itoUniformRefinedCoefficient T N M hM F k) :=
  (hF (itoUniformCoarseIndex N M hM k)).comp
    (itoPastRestriction_measurable _ _ _)

/-- Actual sampled paths restrict literally to the actual coarse sampled past. -/
theorem itoUniformRefinedCoefficient_actual_history {X : Type*}
    (T : ℝ≥0) (N M : ℕ) (hM : 0 < M)
    (F : (i : Fin N) → (Set.Iic (itoUniformNNTime T N i) → X) → ℝ)
    (B : ℝ≥0 → X) (k : Fin (N*M)) :
    itoUniformRefinedCoefficient T N M hM F k (fun u => B u) =
      F (itoUniformCoarseIndex N M hM k) (fun u => B u) := rfl

end
end GinibrePoincare
