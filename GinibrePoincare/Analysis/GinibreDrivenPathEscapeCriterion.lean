module

public import GinibrePoincare.Analysis.GinibreDrivenPathCompactRestart

@[expose] public section

/-! # Concrete boundedness and separation criterion for genuine continuation -/
open Set Metric MeasureTheory
open scoped Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 def ginibreSeparatedBoundedConfigurations (n : ℕ) (R δ : ℝ) : Set (Configuration n) :=
  {z | ‖z‖ ≤ R ∧ ∀ i j, i ≠ j → δ ≤ ‖z i-z j‖}

 theorem ginibreSeparatedBoundedConfigurations_compact (n : ℕ) (R δ : ℝ) :
    IsCompact (ginibreSeparatedBoundedConfigurations n R δ) := by
  have hsep : IsClosed {z : Configuration n | ∀ i j, i ≠ j → δ ≤ ‖z i-z j‖} := by
    simp only [setOf_forall]
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    apply isClosed_iInter
    intro hij
    have hn : Continuous (fun z : Configuration n => ‖z i-z j‖) :=
      ((continuous_apply i).sub (continuous_apply j)).norm
    exact isClosed_le continuous_const hn
  have hc : IsClosed (ginibreSeparatedBoundedConfigurations n R δ) :=
    (isClosed_le continuous_norm continuous_const).inter hsep
  apply (isCompact_closedBall (0 : Configuration n) R).of_isClosed_subset hc
  intro z hz
  simpa only [mem_closedBall, dist_zero_right] using hz.1

 theorem ginibreSeparatedBoundedConfigurations_collisionFree (n : ℕ) (R δ : ℝ) (hδ : 0 < δ)
    (z : Configuration n) (hz : z ∈ ginibreSeparatedBoundedConfigurations n R δ) : CollisionFree z := by
  intro i j hij
  by_contra hne
  have h := hz.2 i j hne
  rw [hij, sub_self, norm_zero] at h
  linarith

 theorem ginibreDrivenPath_extend_of_bounded_separated (n : ℕ) (α : ℝ)
    (N X : ℝ → Configuration n) (hN : Continuous N) (T : ℝ) (hT : 0 < T)
    (hX : ContinuousOn X (Ico 0 T))
    (hInt : ∀ t ∈ Ico 0 T, IntervalIntegrable (fun u => ginibreLangevinDrift n α (X u)) volume 0 t)
    (hEq : ∀ t ∈ Ico 0 T, X t = X 0+N t+∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (X u))
    (R δ : ℝ) (hδ : 0 < δ) (hbound : ∀ t ∈ Ico 0 T, ‖X t‖ ≤ R)
    (hsep : ∀ t ∈ Ico 0 T, ∀ i j, i ≠ j → δ ≤ ‖X t i-X t j‖) :
    ∃ ε > (0 : ℝ), ∃ U : ℝ → Configuration n, EqOn U X (Ico 0 T) ∧
      ContinuousOn U (Icc 0 (T+ε)) ∧
      ∀ t ∈ Icc 0 (T+ε), CollisionFree (U t) ∧
        IntervalIntegrable (fun u => ginibreLangevinDrift n α (U u)) volume 0 t ∧
        U t = U 0+N t+∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (U u) := by
  exact ginibreDrivenPath_compact_extend_beyond n α N X hN T hT hX hInt hEq
    (ginibreSeparatedBoundedConfigurations n R δ)
    (ginibreSeparatedBoundedConfigurations_compact n R δ)
    (ginibreSeparatedBoundedConfigurations_collisionFree n R δ hδ)
    (fun t ht => ⟨hbound t ht, hsep t ht⟩)

end
end GinibrePoincare
