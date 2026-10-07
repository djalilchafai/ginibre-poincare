module

public import GinibrePoincare.Analysis.GinibreHamiltonianSublevels
public import GinibrePoincare.Analysis.GinibreDrivenPathCompactRestart

@[expose] public section

/-! Actual Hamiltonian control implies continuation of the singular driven equation. -/
open Set MeasureTheory
open scoped Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem ginibreDrivenPath_extend_of_hamiltonian_bounded {n : ℕ} (hn : 0 < n) (α : ℝ)
    (N X : ℝ → Configuration n) (hN : Continuous N) (T : ℝ) (hT : 0 < T)
    (hX : ContinuousOn X (Ico 0 T))
    (hInt : ∀ t ∈ Ico 0 T, IntervalIntegrable (fun u => ginibreLangevinDrift n α (X u)) volume 0 t)
    (hEq : ∀ t ∈ Ico 0 T, X t = X 0+N t+∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (X u))
    (hfree : ∀ t ∈ Ico 0 T, CollisionFree (X t))
    (B : ℝ) (hbound : ∀ t ∈ Ico 0 T, ginibreHamiltonian n (X t) ≤ B) :
    ∃ δ > (0 : ℝ), ∃ U : ℝ → Configuration n, EqOn U X (Ico 0 T) ∧
      ContinuousOn U (Icc 0 (T+δ)) ∧
      ∀ t ∈ Icc 0 (T+δ), CollisionFree (U t) ∧
        IntervalIntegrable (fun u => ginibreLangevinDrift n α (U u)) volume 0 t ∧
        U t = U 0+N t+∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (U u) := by
  exact ginibreDrivenPath_compact_extend_beyond n α N X hN T hT hX hInt hEq
    (ginibreHamiltonianSublevel n B) (ginibreHamiltonianSublevel_isCompact hn B)
    (fun z hz => hz.1) (fun t ht => ⟨hfree t ht, hbound t ht⟩)

 theorem ginibreDrivenPath_finite_nonextendible_hamiltonian_unbounded {n : ℕ}
    (hn : 0 < n) (α : ℝ) (N X : ℝ → Configuration n) (hN : Continuous N)
    (T : ℝ) (hT : 0 < T) (hX : ContinuousOn X (Ico 0 T))
    (hInt : ∀ t ∈ Ico 0 T, IntervalIntegrable (fun u => ginibreLangevinDrift n α (X u)) volume 0 t)
    (hEq : ∀ t ∈ Ico 0 T, X t = X 0+N t+∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (X u))
    (hfree : ∀ t ∈ Ico 0 T, CollisionFree (X t))
    (hmax : ¬ ∃ δ > (0 : ℝ), ∃ U : ℝ → Configuration n, EqOn U X (Ico 0 T) ∧
      ContinuousOn U (Icc 0 (T+δ)) ∧
      ∀ t ∈ Icc 0 (T+δ), CollisionFree (U t) ∧
        IntervalIntegrable (fun u => ginibreLangevinDrift n α (U u)) volume 0 t ∧
        U t = U 0+N t+∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (U u)) :
    ∀ B : ℝ, ∃ t ∈ Ico 0 T, B < ginibreHamiltonian n (X t) := by
  intro B
  by_contra h
  push_neg at h
  exact hmax (ginibreDrivenPath_extend_of_hamiltonian_bounded hn α N X hN T hT hX hInt hEq hfree B h)

end
end GinibrePoincare
