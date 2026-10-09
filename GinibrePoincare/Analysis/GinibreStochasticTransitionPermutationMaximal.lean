module

public import GinibrePoincare.Analysis.GinibreStochasticTransitionPermutationDynamics

@[expose] public section

open Set MeasureTheory
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem ginibreDrivenMaximalLifetime_le_permute {n : ℕ} (σ : ParticlePermutation n)
    (α : ℝ) (N : ℝ → Configuration n) (z : Configuration n) :
    ginibreDrivenMaximalLifetime n α N z ≤
      ginibreDrivenMaximalLifetime n α (fun s => permute σ (N s)) (permute σ z) := by
  apply iSup_le
  intro T
  obtain ⟨X, hX⟩ := T.property
  exact ginibreDrivenHorizons_le_lifetime ⟨fun s => permute σ (X s), ginibreDrivenSegment_permute hX σ⟩

theorem ginibreDrivenMaximalLifetime_permute {n : ℕ} (σ : ParticlePermutation n)
    (α : ℝ) (N : ℝ → Configuration n) (z : Configuration n) :
    ginibreDrivenMaximalLifetime n α (fun s => permute σ (N s)) (permute σ z)=
      ginibreDrivenMaximalLifetime n α N z := by
  apply le_antisymm
  · have hi := ginibreDrivenMaximalLifetime_le_permute σ.symm α
      (fun s => permute σ (N s)) (permute σ z)
    have hz : permute σ.symm (permute σ z)=z := by
      funext i
      exact congrArg z (σ.apply_symm_apply i)
    have hN : (fun s => permute σ.symm (permute σ (N s)))=N := by
      funext s i
      exact congrArg (N s) (σ.apply_symm_apply i)
    rw [hz, hN] at hi
    exact hi
  · exact ginibreDrivenMaximalLifetime_le_permute σ α N z

theorem ginibreDrivenMaximalValue_permute {n : ℕ} (σ : ParticlePermutation n)
    (α : ℝ) (N : ℝ → Configuration n) (z : Configuration n) (t : ℝ≥0) :
    ginibreDrivenMaximalValue n α (fun s => permute σ (N s)) (permute σ z) t=
      permute σ (ginibreDrivenMaximalValue n α N z t) := by
  have hl := ginibreDrivenMaximalLifetime_permute σ α N z
  by_cases ht : (t : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N z
  · obtain ⟨T, X, hT, hX⟩ := ginibreDrivenMaximalLifetime_exists_segment t ht
    have hXp := ginibreDrivenSegment_permute hX σ
    have hp : (t : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α
        (fun s => permute σ (N s)) (permute σ z) := by rw [hl]; exact ht
    rw [ginibreDrivenMaximalValue_eq_segment hXp t hT.le hp,
      ginibreDrivenMaximalValue_eq_segment hX t hT.le ht]
  · simp only [ginibreDrivenMaximalValue, hl, dif_neg ht]

#print axioms ginibreDrivenMaximalLifetime_permute
#print axioms ginibreDrivenMaximalValue_permute
end
end GinibrePoincare
