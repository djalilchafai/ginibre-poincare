module

public import GinibrePoincare.Analysis.GinibreHamiltonianContinuation
public import GinibrePoincare.Analysis.GinibreDrivenPathLocalStability
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

@[expose] public section

/-! Genuine uniqueness on every finite collision-free interval. -/
open Set MeasureTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem ginibreLangevinDrift_lipschitzOn_compact (n : ℕ) (α : ℝ)
    (K : Set (Configuration n)) (hK : IsCompact K)
    (hcf : ∀ z ∈ K, CollisionFree z) :
    ∃ L, LipschitzOnWith L (ginibreLangevinDrift n α) K := by
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
  intro z hz
  obtain ⟨L, U, hU, hb⟩ := ginibreLangevinDrift_local_lipschitz n α z (hcf z hz)
  exact ⟨L, U, mem_nhdsWithin_of_mem_nhds hU, hb⟩

 theorem ginibreDrivenPath_finite_interval_unique (n : ℕ) (α : ℝ)
    (z : Configuration n) (N X Y : ℝ → Configuration n) (T : ℝ) (hT : 0 ≤ T)
    (hX : ContinuousOn X (Icc 0 T)) (hY : ContinuousOn Y (Icc 0 T))
    (hXcf : ∀ t ∈ Icc 0 T, CollisionFree (X t))
    (hYcf : ∀ t ∈ Icc 0 T, CollisionFree (Y t))
    (hEqX : ∀ t ∈ Icc 0 T, X t = z+N t+∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (X u))
    (hEqY : ∀ t ∈ Icc 0 T, Y t = z+N t+∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (Y u)) :
    EqOn X Y (Icc 0 T) := by
  let K := X '' Icc 0 T ∪ Y '' Icc 0 T
  have hK : IsCompact K := (isCompact_Icc.image_of_continuousOn hX).union
    (isCompact_Icc.image_of_continuousOn hY)
  have hcf : ∀ x ∈ K, CollisionFree x := by
    rintro x (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact hXcf t ht
    · exact hYcf t ht
  obtain ⟨L, hb⟩ := ginibreLangevinDrift_lipschitzOn_compact n α K hK hcf
  obtain ⟨g, hg, heq⟩ := hb.extend_finite_dimension
  have hXg (t : ℝ) (ht : t ∈ Icc 0 T) : X t = z+N t+∫ u in (0 : ℝ)..t, g (X u) := by
    rw [hEqX t ht]
    congr 1
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht.1] at hu
    exact heq (Or.inl ⟨u, ⟨hu.1, hu.2.trans ht.2⟩, rfl⟩)
  have hYg (t : ℝ) (ht : t ∈ Icc 0 T) : Y t = z+N t+∫ u in (0 : ℝ)..t, g (Y u) := by
    rw [hEqY t ht]
    congr 1
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht.1] at hu
    exact heq (Or.inr ⟨u, ⟨hu.1, hu.2.trans ht.2⟩, rfl⟩)
  have hu := drivenVolterra_lipschitz_stability_on g _ hg z N N X Y T 0 hT le_rfl
    hX hY hXg hYg (fun t ht => by simp)
  intro t ht
  have hz := hu t ht
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using hz

end
end GinibrePoincare
