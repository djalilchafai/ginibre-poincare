module

public import GinibrePoincare.Analysis.GinibreHamiltonianMaximalNoiseStability
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.Semicontinuity.Basic

@[expose] public section

/-! Genuine openness and measurability of the constructed maximal lifespan. -/
open Set Metric MeasureTheory Filter
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Continuous additive driving paths starting at zero, with compact-open topology. -/
def GinibreContinuousNoise (n : ℕ) := {N : C(ℝ, Configuration n) // N 0 = 0}

instance (n : ℕ) : TopologicalSpace (GinibreContinuousNoise n) := inferInstanceAs (TopologicalSpace {N : C(ℝ, Configuration n) // N 0 = 0})
instance (n : ℕ) : MeasurableSpace (GinibreContinuousNoise n) := borel _
instance (n : ℕ) : BorelSpace (GinibreContinuousNoise n) := ⟨rfl⟩

 theorem ginibreDrivenMaximalLifetime_alive_isOpen {n : ℕ} (hn : 0 < n)
    (α : ℝ) (z : Configuration n) (T : ℝ≥0) :
    IsOpen {N : GinibreContinuousNoise n | (T : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N.val z} := by
  rw [isOpen_iff_mem_nhds]
  intro N hN
  obtain ⟨δ, hδ, hp⟩ := ginibreDrivenMaximalLifetime_uniform_noise_neighborhood hn α N.val z T hN
  have hc : Continuous (fun M : GinibreContinuousNoise n =>
      ‖N.val.restrict (Icc 0 (T : ℝ))-M.val.restrict (Icc 0 (T : ℝ))‖) :=
    (continuous_const.sub ((ContinuousMap.continuous_restrict _).comp continuous_subtype_val)).norm
  have ho : IsOpen {M : GinibreContinuousNoise n |
      ‖N.val.restrict (Icc 0 (T : ℝ))-M.val.restrict (Icc 0 (T : ℝ))‖ < δ} :=
    isOpen_lt hc continuous_const
  apply Filter.mem_of_superset (ho.mem_nhds (by simp only [Set.mem_setOf_eq, sub_self, norm_zero]; exact hδ))
  intro M hM
  apply hp M.val M.val.continuous M.property
  intro t ht
  have h := ContinuousMap.norm_coe_le_norm
    (N.val.restrict (Icc 0 (T : ℝ))-M.val.restrict (Icc 0 (T : ℝ))) ⟨t, ht⟩
  exact h.trans hM.le

 theorem ginibreDrivenMaximalLifetime_lowerSemicontinuous {n : ℕ} (hn : 0 < n)
    (α : ℝ) (z : Configuration n) :
    LowerSemicontinuous (fun N : GinibreContinuousNoise n => ginibreDrivenMaximalLifetime n α N.val z) := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro a
  by_cases ha : a = ⊤
  · subst a
    simp
  · rw [← ENNReal.coe_toNNReal ha]
    exact ginibreDrivenMaximalLifetime_alive_isOpen hn α z a.toNNReal

 theorem ginibreDrivenMaximalLifetime_measurable {n : ℕ} (hn : 0 < n)
    (α : ℝ) (z : Configuration n) :
    Measurable (fun N : GinibreContinuousNoise n => ginibreDrivenMaximalLifetime n α N.val z) :=
  (ginibreDrivenMaximalLifetime_lowerSemicontinuous hn α z).measurable

end
end GinibrePoincare
